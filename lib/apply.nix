# The door: Reynolds 1972 §6's one `apply` function, interpreting the records `defunctionalize` wrote.
# The ONLY place in gen a closure is applied (design Q8 (c′)). Its call is the unifying spec's (§2.8):
#   { id; context; sources; captured ? null; } -> Either { output; scope; }
# and every refusal is a value (`{ left = { code; witness; }; }`), never a throw (ADR-0025 item 1).
{
  T,
  aspects,
  program,
  walk,
}:
let
  W = walk;
  tm = T.term;
  inherit (builtins)
    all
    attrNames
    concatMap
    filter
    fromJSON
    head
    intersectAttrs
    isAttrs
    isList
    listToAttrs
    match
    ;
  ok = v: { right = v; };
  shortId = id: if builtins.stringLength id > 120 then builtins.substring 0 120 id + "…" else id;
  refuse = code: witness: { left = { inherit code witness; }; };
  # THE IDENTIFY STEP IS TOTAL. An id is decoded only once it matches refId's whole grammar, because
  # `fromJSON` aborts uncatchably on malformed input on all three evaluators, and a prefix match
  # (`{"declared":…`) lets a truncated or ill-shaped record through to the decode. The grammar is
  # unit 1's encoding (`toJSON` of a one-key `declared`/`nested` record, keys sorted), written as
  # gen-aspects writes it for the same decode. The length is bounded before any match: `match`
  # overflows the C++ stack on a long subject (64002 characters on nix and Determinate), so the bound
  # is a quarter of the measured ceiling, nesting depth 7 at refId's growth (den v1's maximum is 3).
  maxIdLength = 8192;
  jstr = "\"([^\\\\\"]|\\\\([\"\\\\/bfnrt]|u[0-9a-fA-F]{4}))*\"";
  jseg = "(${jstr}|-?[0-9]+)";
  jstrs = "(${jstr}(,${jstr})*)?";
  jreads = "(null|\\[${jstrs}])";
  rxDeclared = "[{]\"declared\":[{]\"reads\":${jreads},\"site\":${jstr}[}][}]";
  rxNested = "[{]\"nested\":[{]\"outer\":${jstr},\"position\":\\[(${jseg}(,${jseg})*)?],\"reads\":${jreads},\"sources\":[{](${jstr}:${jstr}(,${jstr}:${jstr})*)?[}][}][}]";
  decode =
    id:
    if
      builtins.isString id
      && builtins.stringLength id <= maxIdLength
      && (match rxDeclared id != null || match rxNested id != null)
    then
      fromJSON id
    else
      null;
  # The registration a (possibly nested) identifier descends from: `null` when any `outer` on the
  # chain is not itself refId's encoding.
  rootOf =
    d:
    if d == null then
      null
    else if d ? declared then
      d
    else
      rootOf (decode d.nested.outer);
  genAttrs =
    ns: f:
    listToAttrs (
      map (n: {
        name = n;
        value = f n;
      }) ns
    );

  mkApply =
    {
      lambdas,
      cnf,
      declared ? null,
      entityKinds ? null,
    }:
    let
      # What the closure receives (0cmbt R4/R8, moved here from gen-aspects' context door). A formals
      # pattern is narrowed to its formals; an open pattern gets D, narrowed to E where E is declared
      # (unifying §2.8, UP3); `{ }:` gets `{ }`.
      received =
        p: context:
        if p.kind == "formals" then
          let
            missing = filter (n: !(context ? ${n})) p.required;
          in
          if missing != [ ] then
            refuse "required-coordinate-absent" {
              inherit missing;
              message = "the closure requires coordinate(s) ${builtins.toJSON missing} that the context does not carry; its door node's condition `has` should have kept it from firing";
            }
          else
            ok (intersectAttrs p.formals context)
        else if p.kind == "open" then
          let
            d = if declared == null then context else intersectAttrs (genAttrs declared (_: null)) context;
          in
          ok (if entityKinds == null then d else intersectAttrs (genAttrs entityKinds (_: null)) d)
        else
          ok { };

      # The guard codomain: aspect content (an attrset, or a module function of `cnf.moduleArgs`),
      # lowered with the same walk, every closure at an aspect position a nested door node. A module
      # function, the whole output or nested, passes through `mode.moduleFn`: its result is checked
      # when the module system applies it, and a closure in it is refused by name.
      lowerGuard =
        mode: v:
        if (isAttrs v && !(v ? __functor)) || (W.isCallable v && aspects.mkIsModuleFn cnf v) then
          let
            w = (W.walk mode).aspectAt [ ] v;
          in
          if w.bad != [ ] then
            refuse "guard-codomain" {
              position = (head w.bad).pos;
              message = "the closure's output holds ${(head w.bad).why} at ${builtins.toJSON (head w.bad).pos}";
            }
          else
            ok w
        else
          refuse "guard-codomain" {
            position = [ ];
            message = "a closure at an aspect position returns aspect content: an attrset, or a module function of `cnf.moduleArgs`; this one returned a ${builtins.typeOf v}";
          };

      # The rule codomain: fired declarations of gen-program's rows, each inside the declared contract,
      # and closures (nested door rules). The check is gen-program's own (`codomainBreaches`), so the
      # row table has one home. A `null` `binds`/`suppresses` is the over-approximation, and the check
      # itself reads it as admitting every name of its field: a door rule declaring it FIRES, so `null`
      # is an admission at the firing, never a refusal (the over-approximation refusal belongs to a head
      # analysis, deferred) and never an abort.
      lowerRule =
        contract: mode: v:
        if !isList v then
          refuse "rule-codomain" {
            message = "a rule closure returns a list of declarations; this one returned a ${builtins.typeOf v}";
          }
        else
          let
            ws = builtins.genList (
              i:
              let
                x = builtins.elemAt v i;
              in
              if W.isCallable x then (W.walk mode).aspectAt [ i ] x else W.leaf x
            ) (builtins.length v);
            decls = filter (x: !(isAttrs x && x ? body && !(x ? ctor))) (map (w: w.value) ws);
            fields = [
              "emits"
              "binds"
              "suppresses"
            ];
            found = program.codomainBreaches contract decls;
            shapeBad = filter (b: b.field == "shape") found;
            breaches = filter (b: b.names != [ ]) (
              map (field: {
                inherit field;
                names = map (b: b.delta) (filter (b: b.field == field) found);
              }) fields
            );
          in
          if shapeBad != [ ] then
            refuse "rule-codomain" {
              message = "the rule's output holds ${(head shapeBad).delta}; gen-program's rows know ${builtins.toJSON program.ctorNames}";
            }
          else if breaches != [ ] then
            refuse "codomain-breach" {
              inherit breaches;
              message = "the rule's output breached the codomain declared at its registration: ${
                builtins.concatStringsSep "; " (map (b: "${b.field} lacks ${builtins.toJSON b.names}") breaches)
              }";
            }
          else
            ok (W.combine ws // { value = map (w: w.value) ws; });

      self =
        {
          id,
          context,
          sources,
          captured ? null,
        }:
        let
          d = decode id;
          root = rootOf d;
          rootId = builtins.toJSON root;
          reg = lambdas.${rootId} or null;
          # The nested node's recovered context: the outer's received coordinates by their sources.
          rebound =
            if d ? nested then
              filter (n: (sources.${n} or null) != d.nested.sources.${n}) (attrNames d.nested.sources)
            else
              [ ];
          fallback = self {
            id = d.nested.outer;
            context = intersectAttrs d.nested.sources context;
            inherit sources;
          };
          fn =
            if d ? declared then
              reg.fn
            else if captured != null then
              captured
            else if fallback ? left then
              null
            else
              fallback.right.scope.${id} or null;
          p = W.patternOf fn;
          # Nested identifiers: r′ = (outer, sources received, position, the inner's own reads).
          mode = {
            inherit cnf declared;
            strict = true;
            # A module function in the output is applied by the module system, under arguments the door
            # never holds, so a closure its result writes can be neither registered nor scoped: the
            # result passes the output's own check when applied, and a closure in it is refused by name.
            # The envelope is the loader's (defunctionalize.nix `moduleFn`), under its precondition.
            moduleFn =
              pos: f:
              { config, ... }:
              {
                imports = [
                  {
                    __functionArgs = builtins.functionArgs f;
                    # lazy and positional, as the loader's refusals are: a closure throws only when
                    # the merge forces its position, so the check adds no strictness (Section 3 (b))
                    __functor =
                      _: args:
                      (
                        (W.walk (
                          mode
                          // {
                            strict = false;
                            where = "gen-rules.mkApply: the closure registered under ${shortId rootId} returned a module function whose result";
                            idOf =
                              p: _:
                              throw "gen-rules.mkApply: guard-codomain: the closure registered under ${shortId rootId} returned a module function whose result holds a closure at ${builtins.toJSON p}; the door cannot register it, because it exists only under the module system's arguments. Write the closure in an attrset output, where it becomes a nested door node, or as a guard term.";
                            node =
                              _: r: _:
                              r;
                          }
                        )).aspectAt
                          pos
                          (f args)
                      ).value;
                  }
                ];
              };
            idOf =
              pos: q:
              (T.refId {
                nested = {
                  outer = id;
                  sources = intersectAttrs got.right sources;
                  position = pos;
                  inherit (q) reads;
                };
              }).right;
            node =
              condition: ref: q:
              if reg.codomain == "guard" then
                aspects.guard (tm.all (
                  map tm.has (attrNames (intersectAttrs got.right sources)) ++ [ condition ]
                )) ref
              else
                {
                  when = tm.all (map tm.has (attrNames (intersectAttrs got.right sources)) ++ [ condition ]);
                  body = ref;
                  inherit (reg.codomain) emits binds suppresses;
                };
          };
          got = received p context;
          lowered =
            if reg.codomain == "guard" then
              lowerGuard mode (fn got.right)
            else
              lowerRule reg.codomain mode (fn got.right);
        in
        if root == null then
          refuse "not-a-registration" {
            id = if builtins.isString id then shortId id else builtins.typeOf id;
            message = "the door resolves registration identifiers (refId's `declared`/`nested` records); ${
              if builtins.isString id then shortId id else "a ${builtins.typeOf id}"
            } is not one";
          }
        else if reg == null then
          refuse "unregistered" {
            inherit id;
            message = "no closure is registered under ${rootId}; the framework's loader registers each closure it lowers";
          }
        else if rebound != [ ] then
          refuse "source-rebound" {
            coordinate = head rebound;
            recorded = d.nested.sources.${head rebound};
            found = sources.${head rebound} or null;
            message = "the nested closure was written for coordinate ${head rebound} from ${
              d.nested.sources.${head rebound}
            }, and this context supplies it from ${toString (sources.${head rebound} or "nowhere")}";
          }
        else if d ? nested && captured == null && fallback ? left then
          fallback
        else if fn == null then
          refuse "unregistered" {
            inherit id;
            message = "re-applying the outer did not produce a closure at ${builtins.toJSON d.nested.position}";
          }
        else if got ? left then
          got
        else if lowered ? left then
          lowered
        else
          ok {
            output = lowered.right.value;
            scope = listToAttrs (
              map (x: {
                name = x.id;
                value = x.fn;
              }) lowered.right.found
            );
          };
    in
    self;
in
{
  inherit mkApply decode;
}
