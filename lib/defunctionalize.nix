# The lowering at the framework's loader (design Section 3 (b)–(d), Section 4 "one lowering, run at two
# sites"). Reynolds 1972 §6: each closure written at an aspect or rule position becomes a record — a door
# node or door rule whose body is `ref r` — and the closure itself is registered under `r` in `lambdas`,
# the table the one `apply` function interprets. Nothing is applied here.
{
  T,
  aspects,
  merge,
  walk,
}:
let
  W = walk;
  inherit (builtins)
    attrNames
    elemAt
    foldl'
    genList
    head
    isAttrs
    isFunction
    isList
    isPath
    length
    listToAttrs
    mapAttrs
    tail
    toJSON
    unsafeDiscardStringContext
    ;

  # The registration table: an option gen-rules declares and the framework mounts at a path of its
  # choosing (design Section 3 (c)). Lazy: a lookup of `r` forces the table along `r` only.
  lambdas = merge.mkOption {
    type = merge.lazyAttrsOf merge.raw;
    default = { };
    description = "registered lambdas: registration identifier -> { fn; codomain; }";
  };

  # `site` is the closure's declaration identity under 0cmbt §1's key rule: the module's key, then the
  # position (aspect path, key, list index, fragment). A context-free string (unifying §2.8 domain);
  # string context is discarded because the identifier names a declaration and builds nothing.
  siteOf =
    key: pos:
    unsafeDiscardStringContext (toJSON [
      key
      pos
    ]);
  idOf =
    key: pos: p:
    let
      r = T.refId {
        declared = {
          site = siteOf key pos;
          inherit (p) reads;
        };
      };
    in
    if r ? right then
      r.right
    else
      throw "gen-rules.defunctionalize: ${r.left.code}: ${r.left.witness.message}";

  # An inline import with neither a path nor a `key` is keyed by its parent's key and its index,
  # `<parent>` + "#imports." + `<i>` (0cmbt §1's positional rule). The separator is spelled by its code
  # point so that no `#` stands inside a string literal, which the purity scan's comment strip relies on.
  anonImport = builtins.fromJSON ''"\u0023imports."'';

  fullFormKeys = [
    "config"
    "options"
    "imports"
    "_file"
    "key"
    "disabledModules"
    "meta"
    "freeformType"
    "_class"
  ];
  isFullForm = m: builtins.any (k: m ? ${k}) fullFormKeys;

  setAt =
    p: v:
    foldl' (acc: k: { ${k} = acc; }) v (builtins.genList (i: elemAt p (length p - 1 - i)) (length p));

  # Descend to an option path through plain attrsets and property wrappers, and lower there.
  descend =
    path: v: f:
    if path == [ ] then
      f v
    else if isAttrs v && v ? _type then
      W.leaf v # a wrapper above a declared path: carried; the spec's open item O-4 (prototype scope)
    else if isAttrs v && v ? ${head path} then
      let
        w = descend (tail path) v.${head path} f;
      in
      w
      // {
        value = v // {
          ${head path} = w.value;
        };
      }
    else
      W.leaf v;

  defunctionalize =
    {
      cnf,
      declared ? null,
      key,
      lambdasPath,
      aspectPaths ? [ ],
      rulePaths ? [ ],
    }:
    let
      guardMode = k: {
        inherit cnf declared;
        where = k;
        idOf = idOf k;
        node =
          condition: ref: _:
          aspects.guard condition ref;
      };
      ruleMode = k: contract: {
        inherit cnf declared;
        where = k;
        idOf = idOf k;
        node = condition: ref: _: {
          when = condition;
          body = ref;
          inherit (contract) emits binds suppresses;
        };
      };
      # At a rule position the value is a list or an attrset of rules; a closure element is a door rule.
      rulesAt =
        m: pos: v:
        let
          w = W.walk m;
          one = p: x: if W.isCallable x then (W.walk m).aspectAt p x else W.leaf x;
        in
        if isList v then
          let
            ws = genList (i: one (pos ++ [ i ]) (elemAt v i)) (length v);
          in
          W.combine ws // { value = map (x: x.value) ws; }
        else if isAttrs v && v ? _type then
          w.wrapperAt pos v (rulesAt m)
        else if isAttrs v then
          let
            ws = mapAttrs (n: x: one (pos ++ [ n ]) x) v;
          in
          W.combine (builtins.attrValues ws) // { value = mapAttrs (_: x: x.value) ws; }
        else
          one pos v;

      lowerConfig =
        k: c:
        let
          aspectSteps = map (p: cfg: descend p cfg (v: (W.walk (guardMode k)).aspectAt p v)) aspectPaths;
          ruleSteps = map (
            r: cfg: descend r.path cfg (v: rulesAt (ruleMode k r.contract) r.path v)
          ) rulePaths;
          step =
            acc: f:
            let
              w = f acc.value;
            in
            {
              inherit (w) value;
              found = acc.found ++ map (x: x // { codomain = "guard"; }) w.found;
              bad = acc.bad ++ w.bad;
            };
          stepRule =
            acc: r:
            let
              w = descend r.path acc.value (v: rulesAt (ruleMode k r.contract) r.path v);
            in
            {
              inherit (w) value;
              found = acc.found ++ map (x: x // { codomain = r.contract; }) w.found;
              bad = acc.bad ++ w.bad;
            };
          afterAspects = foldl' step (W.leaf c) aspectSteps;
          done = foldl' stepRule afterAspects rulePaths;
          regs = listToAttrs (
            map (x: {
              name = x.id;
              value = {
                inherit (x) fn codomain;
              };
            }) done.found
          );
        in
        (merge.mkMerge [
          done.value
          (setAt lambdasPath regs)
        ]);

      lowerModule =
        k: m:
        if isPath m then
          {
            key = toString m;
            _file = m;
            imports = [ (lowerModule (toString m) (import m)) ];
          }
        else if W.isCallable m then
          # A top-level module function: wrapped, never applied here; the wrapper keeps its formals,
          # so gen-merge applies it by them (precondition unit 0, den-hoag-...-u6lf8).
          {
            __functionArgs = builtins.functionArgs m;
            __functor = _: args: lowerModule k (m args);
          }
        else if isAttrs m && isFullForm m then
          let
            k' = m.key or k;
          in
          m
          // {
            config = lowerConfig k' (m.config or { });
            imports = genList (
              i:
              let
                x = elemAt (m.imports or [ ]) i;
              in
              lowerModule (if isPath x then toString x else "${k'}${anonImport}${toString i}") x
            ) (length (m.imports or [ ]));
          }
        else if isAttrs m then
          { config = lowerConfig k m; }
        else
          m;
    in
    lowerModule key;
in
{
  inherit defunctionalize lambdas siteOf;
}
