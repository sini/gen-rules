# The one lowering's traversal (design Section 3 (b)), shared by its two sites: the framework's loader
# (defunctionalize.nix) and the door's own output (apply.nix). A lazy, structure-preserving map over an
# aspect-tree value. Positions come from gen-aspects' published classification surface (`keyCategory`),
# never a parallel membership list; a context closure is told from a module function by `mkIsModuleFn`.
#
# Each step returns `{ value; found; bad; }`, all three lazy and sharing one child walk: `value` is the
# lowered tree, `found` the closures met (position, id, closure), `bad` the functions no rule admits.
{ T, aspects }:
let
  tm = T.term;
  inherit (builtins)
    all
    attrNames
    concatLists
    elem
    elemAt
    filter
    functionArgs
    genList
    isAttrs
    isFunction
    isList
    length
    listToAttrs
    mapAttrs
    match
    removeAttrs
    toXML
    ;
  genAttrs =
    ns: f:
    listToAttrs (
      map (n: {
        name = n;
        value = f n;
      }) ns
    );

  # The closure's pattern under 0cmbt R4/R8, read exactly as gen-aspects' context door reads it today
  # (`require-wrapped-closure.nix` `requireContextOf`, which retires to here: design Section 3, rework
  # note). `functionArgs` is `{ }` for `x:`, `{ ... }:` and `{ }:` alike, so the pattern is read from
  # the closure's XML.
  patternOf =
    f:
    let
      raw = if isAttrs f then f.__functor f else f;
      formals = if isAttrs f then f.__functionArgs or (functionArgs raw) else functionArgs f;
      xml = toXML raw;
      hasRe = re: match re xml != null;
    in
    if formals != { } then
      {
        kind = "formals";
        inherit formals;
        required = filter (n: !formals.${n}) (attrNames formals);
        reads = attrNames formals;
      }
    else if hasRe ".*<varpat .*" || hasRe ".*<attrspat[^>]*ellipsis=\"1\".*" then
      {
        kind = "open";
        formals = { };
        required = [ ];
        reads = null;
      }
    else if hasRe ".*<attrspat[^>]*>[[:space:]]*</attrspat>.*" then
      {
        kind = "empty";
        formals = { };
        required = [ ];
        reads = [ ];
      }
    else
      {
        kind = "unreadable";
        formals = { };
        required = [ ];
        reads = [ ];
      };

  # The door node's condition (design Section 3 (c)): `has` over the required formals, `always` else.
  conditionOf = p: if p.kind == "formals" then tm.all (map tm.has p.required) else tm.always;

  isCallable = v: isFunction v || (isAttrs v && v ? __functor);
  leaf = v: {
    value = v;
    found = [ ];
    bad = [ ];
  };
  combine = ws: {
    found = concatLists (map (w: w.found) ws);
    bad = concatLists (map (w: w.bad) ws);
  };

  # mode = { cnf; declared; idOf = pos: pattern: id; node = condition: refTerm: pattern: value; }
  walk =
    mode:
    let
      isModuleFn = aspects.mkIsModuleFn mode.cnf;
      category = aspects.keyCategory mode.cnf;
      moduleArgs = mode.cnf.moduleArgs;

      closureAt =
        pos: f:
        let
          p = patternOf f;
          id = mode.idOf pos p;
        in
        if p.kind == "unreadable" then
          {
            # At the loader the refusal is thrown at its position (forced only when that position
            # is read); in the door's output it is the codomain refusal's witness.
            value =
              if mode.strict or false then
                f
              else
                throw "gen-rules.defunctionalize: ${mode.where or ""} at ${builtins.toJSON pos}: a function whose pattern cannot be read (a primop, or a functor whose __functor is not a lambda); write a closure with a formals pattern, an open pattern or `{ }:`";
            found = [ ];
            bad = [
              {
                inherit pos;
                why = "a function whose pattern cannot be read (a primop, or a functor whose __functor is not a lambda)";
              }
            ];
          }
        else
          {
            value = mode.node (conditionOf p) (tm.ref id) p;
            found = [
              {
                inherit pos id;
                fn = f;
                pattern = p;
              }
            ];
            bad = [ ];
          };

      aspectAt =
        pos: v:
        if isFunction v then
          # A module function at an aspect position is NOT entered (design Section 3 (b) wraps it;
          # where its result's closures register is an open owner reading, S1).
          if isModuleFn v then leaf v else closureAt pos v
        else if isAttrs v && v ? __functor then
          # den v1's `__functor` aspect form is the framework's vocabulary (design open item 9): the
          # loader carries it unlowered; in the door's output it is a function gen-aspects would hold.
          if mode.strict or false then
            {
              value = v;
              found = [ ];
              bad = [
                {
                  inherit pos;
                  why = "a `__functor` record at an aspect position (design open item 9: the framework's vocabulary)";
                }
              ];
            }
          else
            leaf v
        else if isAttrs v && ((v.__guard or false) || v ? __bodyTerm) then
          leaf v
        else if isAttrs v && v ? _type then
          wrapperAt pos v aspectAt
        else if isAttrs v then
          attrsAt pos v
        else
          leaf v;

      # The module system's property wrappers: their contents are lowered, never their conditions.
      wrapperAt =
        pos: v: k:
        if
          elem v._type [
            "if"
            "override"
            "order"
          ]
        then
          let
            w = k pos v.content;
          in
          w
          // {
            value = v // {
              content = w.value;
            };
          }
        else if v._type == "merge" then
          let
            ws = genList (
              i:
              k (
                pos
                ++ [
                  "merge"
                  i
                ]
              ) (elemAt v.contents i)
            ) (length v.contents);
          in
          combine ws
          // {
            value = v // {
              contents = map (w: w.value) ws;
            };
          }
        else
          leaf v;

      # In the door's output (mode.strict) a function anywhere but a class key or an aspect position is
      # outside the guard codomain: gen-aspects would hold it as data.
      dataAt =
        pos: v:
        if isCallable v then
          {
            value = v;
            found = [ ];
            bad = [
              {
                inherit pos;
                why = "a function outside a class key or an aspect position";
              }
            ];
          }
        else if isAttrs v then
          let
            ws = mapAttrs (k: dataAt (pos ++ [ k ])) v;
          in
          combine (builtins.attrValues ws) // { inherit (leaf v) value; }
        else if isList v then
          combine (genList (i: dataAt (pos ++ [ i ]) (elemAt v i)) (length v)) // { inherit (leaf v) value; }
        else
          leaf v;

      listAt =
        pos: xs:
        let
          ws = genList (i: aspectAt (pos ++ [ i ]) (elemAt xs i)) (length xs);
        in
        combine ws // { value = map (w: w.value) ws; };

      # At a class key the value is classified and not entered (design Section 3 (b), gate v2 G3). Every
      # field is lazy: the aspect's attribute set never depends on a class value, and a class value is
      # forced only when its own position, or the aspect's `includes` (where a lift lands), is read.
      classAt =
        pos: v:
        let
          fnLike = isCallable v && !(isModuleFn v);
          p = patternOf v;
          coords = filter (n: !(moduleArgs ? ${n})) p.required;
          liftable =
            fnLike
            && p.kind == "formals"
            && coords != [ ]
            && (mode.declared == null || all (n: elem n mode.declared) coords);
          refused = fnLike && !liftable;
          why = "a function at a class key that is neither a module function of `cnf.moduleArgs` nor a closure over declared coordinates";
        in
        {
          value =
            if liftable then
              { }
            else if refused && !(mode.strict or false) then
              throw "gen-rules.defunctionalize: ${mode.where or ""} at ${builtins.toJSON pos}: ${why}; declare a module function of `cnf.moduleArgs`, or a closure at an aspect position"
            else
              v;
          lift =
            if liftable then
              {
                inherit pos coords;
                fn = v;
              }
            else
              null;
          found = [ ];
          bad = if refused then [ { inherit pos why; } ] else [ ];
        };

      # `{ <class> = f; }`, f over coordinates C and module args M, becomes the aspect-position closure
      # `{ C }: { <class> = <f with C applied, M kept> }` (gate v2 G3): a door node in `includes`.
      liftOf =
        k: l:
        let
          margs = removeAttrs (functionArgs l.fn) l.coords;
        in
        {
          __functionArgs = genAttrs l.coords (_: false);
          __functor = _: ctx: {
            ${k} = {
              __functionArgs = margs;
              __functor = _: m: l.fn (m // genAttrs l.coords (n: ctx.${n}));
            };
          };
        };

      attrsAt =
        pos: v:
        let
          ws = mapAttrs (
            k: c:
            let
              cat = category k;
            in
            if k == "includes" && isList c then
              listAt (pos ++ [ k ]) c
            else if cat == "class" then
              classAt (pos ++ [ k ]) c
            else if cat == null then
              aspectAt (pos ++ [ k ]) c
            else if mode.strict or false then
              dataAt (pos ++ [ k ]) c
            else
              leaf c
          ) v;
          classKeys = filter (k: category k == "class") (attrNames v);
          liftWalks = builtins.concatMap (
            k:
            let
              l = ws.${k}.lift;
            in
            if l == null then [ ] else [ (closureAt l.pos (liftOf k l)) ]
          ) classKeys;
          base = if ws ? includes then ws.includes.value else [ ];
          extra = map (w: w.value) liftWalks;
        in
        combine (builtins.attrValues ws ++ liftWalks)
        // {
          value =
            mapAttrs (_: w: w.value) ws
            // (
              if classKeys == [ ] then
                { }
              else
                {
                  includes =
                    if extra == [ ] then
                      base
                    else if isList base then
                      base ++ extra
                    else
                      throw "gen-rules: a lifted class closure lands in `includes`, which is not a list here";
                }
            );
        };
    in
    {
      inherit aspectAt listAt wrapperAt;
    };
in
{
  inherit
    walk
    patternOf
    conditionOf
    isCallable
    leaf
    combine
    ;
}
