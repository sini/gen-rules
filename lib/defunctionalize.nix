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

  # Descend to an option path through plain attrsets and property wrappers, and lower there. A wrapper
  # above the path is passed through as one at it is (`walk.wrapperAt`); `pre` collects its steps, so
  # two contents of one `mkMerge` lower at two positions.
  descend =
    pre: path: v: f:
    if path == [ ] then
      f pre v
    else if isAttrs v && v ? _type then
      W.wrapperAt pre v (pre': v': descend pre' path v' f)
    else if isAttrs v && v ? ${head path} then
      let
        w = descend pre (tail path) v.${head path} f;
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
      # S1 arm (a): the name the framework mounted the table under inside the aspect submodule, read from
      # the mount itself (`cnf.aspectModules`), the one value the door reads too.
      mounts = W.mountsOf cnf;
      mount =
        if mounts == [ ] then
          null
        else if length mounts == 1 then
          head mounts
        else
          throw "gen-rules.defunctionalize: `cnf.aspectModules` holds ${toString (length mounts)} `lambdasMount` entries (${builtins.concatStringsSep ", " mounts}): a framework mounts gen-rules' registration table once.";
      guardMode =
        k:
        {
          inherit cnf declared;
          where = k;
          idOf = idOf k;
          node =
            condition: ref: _:
            aspects.guard condition ref;
        }
        // (
          if mount == null then
            { }
          else
            {
              # The wrapper keeps the function's formals, so `mkIsModuleFn` still classifies it and
              # gen-merge applies it by them; its result is lowered at the aspect it was written at,
              # under the writing module's key, and registers in that aspect's own table. The aspect
              # submodule reads an attrset definition (a functor) as shorthand config, as nixpkgs'
              # submodule does, so the functor is handed over inside a lambda module, gen-aspects'
              # own `_: d.value` idiom.
              moduleFn =
                pos: f:
                { config, ... }:
                {
                  imports = [
                    {
                      __functionArgs = builtins.functionArgs f;
                      __functor =
                        _: args:
                        lowerModule {
                          base = pos;
                          # the applied result is the aspect NODE itself
                          entry = "aspectAt";
                          aspectPaths = [ [ ] ];
                          rulePaths = [ ];
                          lambdasPath = [ mount ];
                        } k (f args);
                    }
                  ];
                };
            }
        );
      # The root reaches every aspect's table through the aspect collection it lives in: one entry per
      # collection, keyed by the collection's path (`walk.addressKey`, never an identifier's spelling),
      # holding the collection's view (`walk.viewOf`). The names are the loader's own paths, so reading
      # the root forces no aspect; the door reads an aspect's table along the registration's own site
      # (`walk.tableAt`), so it forces exactly the positions the merge forces to reach that door node.
      # Keyed, so the module system collects it once however many modules this loader lowered.
      union = {
        key =
          "gen-rules.lambdasMount:"
          + toJSON [
            lambdasPath
            aspectPaths
            mount
          ];
        imports = [
          (
            { config, ... }:
            setAt lambdasPath (
              listToAttrs (
                map (p: {
                  name = W.addressKey p;
                  value = W.viewOf cnf mount (getAt p config);
                }) aspectPaths
              )
            )
          )
        ];
      };
      # The framework's aspect paths name aspect COLLECTIONS, whose keys are aspect names.
      top = {
        base = [ ];
        entry = "collectionAt";
        inherit aspectPaths rulePaths lambdasPath;
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
        at: k: c:
        let
          aspectSteps = map (
            p: cfg: descend [ ] p cfg (pre: v: (W.walk (guardMode k)).${at.entry} (at.base ++ pre ++ p) v)
          ) at.aspectPaths;
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
              w = descend [ ] r.path acc.value (pre: v: rulesAt (ruleMode k r.contract) (pre ++ r.path) v);
            in
            {
              inherit (w) value;
              found = acc.found ++ map (x: x // { codomain = r.contract; }) w.found;
              bad = acc.bad ++ w.bad;
            };
          afterAspects = foldl' step (W.leaf c) aspectSteps;
          done = foldl' stepRule afterAspects at.rulePaths;
          regs = listToAttrs (
            map (x: {
              name = x.id;
              # the record names the identifier it is registered under, the mark of the loader's own
              # records that an aspect table admits (`lambdasMount`)
              value = {
                inherit (x) id fn codomain;
              };
            }) done.found
          );
        in
        (merge.mkMerge [
          done.value
          (setAt at.lambdasPath regs)
        ]);

      lowerModule =
        at: k: m:
        if isPath m then
          {
            key = toString m;
            _file = m;
            imports = [ (lowerModule at (toString m) (import m)) ];
          }
        else if W.isCallable m && (W.patternOf m).kind != "unreadable" then
          # A top-level module function: wrapped, never applied here; the wrapper keeps its formals,
          # so gen-merge applies it by them (precondition unit 0, den-hoag-...-u6lf8).
          {
            __functionArgs = (W.patternOf m).formals;
            __functor = _: args: lowerModule at k (m args);
          }
        else if isAttrs m && isFullForm m then
          let
            k' = m.key or k;
          in
          m
          // {
            config = lowerConfig at k' (m.config or { });
            imports = genList (
              i:
              let
                x = elemAt (m.imports or [ ]) i;
              in
              lowerModule at (if isPath x then toString x else "${k'}${anonImport}${toString i}") x
            ) (length (m.imports or [ ]));
          }
        else if isAttrs m then
          { config = lowerConfig at k m; }
        else
          m;
    in
    if aspectPaths != [ ] && mount == null then
      throw "gen-rules.defunctionalize: `aspectPaths` is set and `cnf.aspectModules` holds no `lambdasMount`: a module function written at an aspect position would be carried unentered, and a closure in its result would reach gen-aspects unlowered (at a class key, delivered with its guard dropped). Mount gen-rules' registration table inside the aspect submodule: put `genRules.lambdasMount \"<name>\"` in `cnf.aspectModules`, and hand that one cnf to `mkAspectSchema`, `defunctionalize` and `mkApply`."
    else if mount != null && !(aspects.mkIsModuleFn cnf ({ config, ... }: { })) then
      throw "gen-rules.defunctionalize: `cnf.aspectModules` mounts gen-rules' registration table, so a module function at an aspect position is handed to gen-aspects inside a `{ config, ... }:` module, and `config` is not in `cnf.moduleArgs`: gen-aspects would read that module as a context closure. Declare `config` in `cnf.moduleArgs` (the module system passes it to every module)."
    else if mount == null then
      lowerModule top key
    else
      m: {
        imports = [
          (lowerModule top key m)
          union
        ];
      };

  # S1 arm (a): the mount. The aspect-submodule module the framework puts in `cnf.aspectModules`; it
  # declares the registration table under `name`, and the walk reads `name` back from the cnf at the
  # loader and at the door alike (`walk.mountsOf`), so the two sites cannot disagree on where it is.
  # Inside the aspect submodule `name` is this table, never a nested aspect: it holds registration
  # records only, and refuses anything else by name.
  lambdasMount = name: {
    key = W.mountKey;
    options.${name} = merge.mkOption {
      inherit (lambdas) type default description;
      apply =
        t:
        let
          bad = builtins.filter (id: !(isAttrs t.${id} && t.${id} ? fn && t.${id} ? codomain)) (attrNames t);
          # a record the loader made names the identifier it registered it under; one that does not was
          # written by hand, and is refused wherever its table is read (ADR-0025 item 1: refused by
          # name, never dropped). The name is a well-formedness check, not provenance: anyone can write
          # it, so a record that names its key and differs is refused where records unite (the door,
          # `walk.registrations`)
          foreign = builtins.filter (id: (t.${id}.id or null) != id) (attrNames t);
        in
        if bad != [ ] then
          throw "gen-rules.lambdasMount: `${name}` is gen-rules' registration table, mounted inside the aspect submodule, and it holds ${toJSON bad}, which are not registration records (`{ fn; codomain; }`): a nested aspect cannot be named `${name}`. Rename the aspect, or mount the table under another name."
        else if foreign != [ ] then
          throw "gen-rules.lambdasMount: `${name}` holds records under ${toJSON foreign} that gen-rules' loader did not make: an aspect's registration table holds only the records the loader registers for the closures it lowers (each names its identifier), or carries with an aspect returned by reference. Write the closure at an aspect position, and the loader registers it."
        else
          t;
    };
  };

  getAt = p: v: foldl' (acc: k: acc.${k} or { }) v p;

in
{
  inherit
    defunctionalize
    lambdas
    lambdasMount
    siteOf
    ;
}
