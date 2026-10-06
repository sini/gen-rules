# The one lowering's traversal (design Section 3 (b)), shared by its two sites: the framework's loader
# (defunctionalize.nix) and the door's own output (apply.nix). A lazy, structure-preserving map over an
# aspect-tree value. Positions come from gen-aspects' published classification surface (`keyCategory`),
# never a parallel membership list; a context closure is told from a module function by `mkIsModuleFn`.
#
# Each step returns `{ value; found; bad; }`, all three lazy and sharing one child walk: `value` is the
# lowered tree, `found` the closures met (position, id, closure), `bad` the functions no rule admits.
{
  T,
  aspects,
  merge,
}:
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
    head
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
  #
  # OPTION (c), documented beside (a) and NOT taken (den-hoag-t5hli R8's added requirement): hand every
  # `functionArgs = { }` shape `{ }`. It is uniform and needs no `toXML`, but a `{ ... }:` is then
  # handed nothing it can read, and a bare positional `ctx:` aspect receives `{ }` as well. Price,
  # measured at gen-rules d933ba8: 3 fixtures declare an open-pattern closure (`ci/tests/door.nix`
  # aspect `open` and rule `open`, `ci/tests/lower.nix` `open`), all `{ ... }@a:`, and each would read
  # `{ }` where it now reads the context restricted to the declared coordinates; 0 are bare
  # positional. (The old home, gen-aspects a8708d1, counted 3 CI fixtures in the measured v1 corpus,
  # design Section 3 "S"; that figure is of the corpus, not of this tree.)
  # OWNER REVIEW FLAGGED (den-hoag-t5hli): this arm depends on `builtins.toXML`, which is strange;
  # the dependency is held for owner review at delivery, and option (c) is the alternative on the table.
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

  # The module system's property wrappers, the four `_type`s gen-merge's `priority.nix` constructs
  # (`mkIf`; `mkMerge`; `mkOverride`, `mkForce`, `mkDefault`, `mkOptionDefault`; `mkOrder`, `mkBefore`,
  # `mkAfter`): their contents are lowered, never their conditions. A property belongs to the definition
  # it wraps and is discharged at the option that definition reaches (gen-merge `pushDownProperties`,
  # `dischargeProperties`), so a lowering that keeps the wrapper and lowers its content commutes with
  # that push-down. `k` is the step of the position the wrapper stands at: every step that can meet a
  # wrapper passes itself, so a wrapper is transparent wherever it stands. Any other `_type` is data,
  # as gen-merge's discharge reads it. The position steps into the wrapper as gen-merge's
  # `dischargePropertiesAt` addresses it (`"content"` for `if` and `override`; `"contents"` and the
  # index for `merge`), so a position is an address into the definition at both sites: the door's scope
  # positions are read as addresses into its output. An `order` wrapper steps `"content"` too, a step
  # `dischargePropertiesAt` does not take (it hands an order marker on as data, and `sortProperties`
  # unwraps it); `"content"` still names the field the door's address walks.
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
        w = k (pos ++ [ "content" ]) v.content;
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
              "contents"
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

  # S1 arm (a): where the root holds an aspect collection, keyed by the collection's path. An
  # identifier is a JSON object, an address a JSON array, so the two never share a spelling.
  addressKey = p: builtins.unsafeDiscardStringContext (builtins.toJSON p);
  # the address of every proper prefix of a position, shortest first
  prefixKeys = pos: genList (i: addressKey (genList (j: elemAt pos j) (i + 1))) (length pos);

  # The root's view of an aspect collection, keyed like it, every field lazy and built once per
  # evaluation, so lookups share it. An aspect's view holds its own table, the views of its nested
  # aspects, and for its `includes` the views of the aspect elements beside one index of their tables
  # (identifier to each record and the element holding it): reading that index forces the list and its
  # elements' own tables, the positions the merge forces to reach any door node in the list, and no
  # condition below them. A key is a nested aspect by its name (gen-aspects' `keyCategory`), told before
  # its value is read, so a class key's condition is never forced.
  viewOf =
    cnf: t: c:
    let
      isNode = v: isAttrs v && !(v.__guard or false) && v ? ${t};
      nested = k: k != t && k != "includes" && aspects.keyCategory cnf k == null;
      nodeView = a: {
        own = a.${t};
        keys = mapAttrs (k: v: if nested k && isNode v then nodeView v else null) a;
        includes =
          let
            els = filter isNode (if isList (a.includes or null) then a.includes else [ ]);
          in
          rec {
            views = map nodeView els;
            held = builtins.zipAttrsWith (_: hs: hs) (
              genList (
                i:
                mapAttrs (_: r: {
                  inherit r;
                  view = elemAt views i;
                }) (elemAt els i).${t}
              ) (length els)
            );
          };
      };
    in
    mapAttrs (_: a: if isNode a then nodeView a else null) c;

  # Every record registered under `id` in a view (`viewOf`), read along `pos`, the position the closure
  # was written at. Each step moves as the merged value does: an aspect name or a nested key to that
  # aspect, `includes` to every aspect element of the list (an element's index is its definition's,
  # never its merged position), and a step the merged value does not hold (a list index, a wrapper's
  # `merge`, a class key) stays. Each aspect reached is asked for `id` once; past an `includes` list
  # holding `id`, only the elements holding it are followed, and past one holding none, every element.
  # A module function's closures register in the table of the aspect the module system applied it in.
  # That is the aspect it was written at, unless gen-aspects coerced it, beside a second definition,
  # into an element of that aspect's `includes`: so where no table on `pos` holds `id`, the `includes`
  # elements of the aspects reached are asked, the deepest aspect first, and the first that holds `id`
  # answers. A lookup forces the aspects along `pos` and the `includes` lists on it, and an aspect's
  # `includes` off it only when the closure's own function sits there. `tableAtOf true` is the lookup
  # for a load-time id, whose record the root holds: it reads only the tables `pos` names, with no
  # coerced home, and past an `includes` list holding no record of `id` it follows no element.
  tableAt = tableAtOf false;
  tableAtOf =
    loadTime: view: pos: id:
    let
      own = vs: concatLists (map (v: if v.own ? ${id} then [ v.own.${id} ] else [ ]) vs);
      held = v: v.includes.held.${id} or [ ];
      none = {
        found = [ ];
        reached = [ ];
      };
      go =
        vs: steps:
        let
          s = head steps;
          moved = filter (v: v != null) (map (v: v.keys.${s} or null) vs);
        in
        if vs == [ ] || !(builtins.any builtins.isString steps) then
          none
        else if s == "includes" then
          let
            hs = concatLists (map held vs);
            next =
              if hs != [ ] then
                map (h: h.view) hs
              else if loadTime then
                [ ]
              else
                concatLists (map (v: v.includes.views) vs);
            r = go next (builtins.tail steps);
          in
          {
            found = map (h: h.r) hs ++ r.found;
            reached = next ++ r.reached;
          }
        else if builtins.isString s then
          let
            r = go (moved ++ filter (v: (v.keys.${s} or null) == null) vs) (builtins.tail steps);
          in
          {
            found = own moved ++ r.found;
            reached = moved ++ r.reached;
          }
        else
          go vs (builtins.tail steps);
      start = view.${head pos} or null;
      r = go [ start ] (builtins.tail pos);
      found = own [ start ] ++ r.found;
      reached = [ start ] ++ r.reached;
      coerced =
        i:
        if i < 0 then
          [ ]
        else
          let
            hs = held (elemAt reached i);
          in
          if hs != [ ] then map (h: h.r) hs else coerced (i - 1);
    in
    if pos == [ ] || start == null then
      [ ]
    else if found != [ ] || loadTime then
      found
    else
      coerced (length reached - 1);

  # Every identifier a root table registers (the `lambdas` the framework reads): the loader's records at
  # the root, and every record in every aspect table the root's collections reach, once each. An
  # instrument's read, never the door's: it forces every aspect, and so every condition on the way.
  # The records under one identifier unite by the door's rule (`==`), and differing ones are refused by
  # name: a record that names its own key passes the mount's check, so this is where it is caught.
  registrations =
    l:
    let
      isAddress = k: builtins.substring 0 1 k == "[";
      ids =
        v:
        map (k: {
          name = k;
          value = v.own.${k};
        }) (attrNames v.own)
        ++ concatLists (map ids (v.includes.views ++ filter (x: x != null) (builtins.attrValues v.keys)));
      inTables = concatLists (
        map (k: concatLists (map ids (filter (x: x != null) (builtins.attrValues l.${k})))) (
          filter isAddress (attrNames l)
        )
      );
      byId = builtins.zipAttrsWith (_: rs: rs) (
        map (k: { ${k} = l.${k}; }) (filter (k: !(isAddress k)) (attrNames l))
        ++ map (p: { ${p.name} = p.value; }) inTables
      );
      dup = filter (k: builtins.any (r: r != head byId.${k}) byId.${k}) (attrNames byId);
    in
    if dup != [ ] then
      throw "gen-rules.registrations: duplicate-registration: ${builtins.toJSON dup} are registered by records that differ"
    else
      attrNames byId;

  # S1 arm (a): the names under which `cnf.aspectModules` mounts gen-rules' registration table inside the
  # aspect submodule (`lambdasMount`). Read here, from the cnf both sites hand the walk, so the loader and
  # the door carry the same key by construction.
  mountKey = "gen-rules.lambdasMount";
  mountsOf =
    cnf:
    map (m: head (attrNames m.options)) (
      filter (m: isAttrs m && (m.key or null) == mountKey) (cnf.aspectModules or [ ])
    );

  # mode = { cnf; declared; idOf = pos: pattern: id; node = condition: refTerm: pattern: value; }
  walk =
    mode:
    let
      isModuleFn = aspects.mkIsModuleFn mode.cnf;
      category = aspects.keyCategory mode.cnf;
      moduleArgs = mode.cnf.moduleArgs;
      tableKeys = mountsOf mode.cnf;

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
          # A module function at an aspect position is NOT entered (design Section 3 (b)): where the
          # framework mounts the table in the aspect submodule (S1 arm (a)), it is wrapped so that its
          # result passes the same lowering when gen-merge applies it. The door's `moduleFn` checks the
          # result instead, refusing a closure in it by name (apply.nix `mkApply`); without one it is
          # carried.
          if isModuleFn v then
            if mode ? moduleFn then
              {
                value = mode.moduleFn pos v;
                found = [ ];
                bad = [ ];
              }
            else
              leaf v
          else
            closureAt pos v
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

      # An aspect COLLECTION (the loader's aspect paths): each key names an aspect, so it is never
      # classified as a class key, `includes` or the mounted table; that happens at a node only.
      collectionAt =
        pos: v:
        if isAttrs v && v ? _type then
          wrapperAt pos v collectionAt
        else if isAttrs v then
          let
            ws = mapAttrs (n: aspectAt (pos ++ [ n ])) v;
          in
          combine (builtins.attrValues ws) // { value = mapAttrs (_: w: w.value) ws; }
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

      includesAt =
        pos: v:
        if isAttrs v && v ? _type then
          wrapperAt pos v includesAt
        else if isList v then
          listAt pos v
        else if mode.strict or false then
          dataAt pos v
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
      #
      # A wrapper at a class key is lowered through like any other (`wrapperAt`), with one exception the
      # lift forces. A lift MOVES the class definition into a node in `includes`: `mkIf` is a condition
      # on that definition alone, so it moves with it, around the class value inside the lifted node's
      # output; the `includes` entry stays plain, so reading `includes` never forces the condition
      # (design Section 3 (b): "it adds no strictness"). `mkMerge` is structure: each content lifts as
      # its own node. An override or order property ranks a definition against its siblings at the
      # option it is discharged at, and the lift changes that option, so a liftable closure under one is
      # refused by name. `lifts` holds each lift with `wrap`, the wrappers its class value carries.
      classAt =
        pos: v:
        if
          isAttrs v
          && v ? _type
          && elem v._type [
            "if"
            "merge"
            "override"
            "order"
          ]
        then
          let
            # the wrapper's own structure, with each lowered content's lifts kept (`wrapperAt` keeps
            # `found` and `bad` only)
            ws =
              if v._type == "merge" then
                genList (
                  i:
                  classAt (
                    pos
                    ++ [
                      "contents"
                      i
                    ]
                  ) (elemAt v.contents i)
                ) (length v.contents)
              else
                [ (classAt (pos ++ [ "content" ]) v.content) ];
            lifts = concatLists (map (w: w.lifts) ws);
            ranked = v._type == "override" || v._type == "order";
            why = "a closure over coordinates at a class key under a property wrapper of `_type = \"${v._type}\"` (`mkOverride`/`mkForce`/`mkDefault`, or `mkOrder`/`mkBefore`/`mkAfter`): the lift moves the definition into `includes`, where that property would rank it against other definitions than the ones it was written beside";
          in
          if ranked && lifts != [ ] then
            {
              value =
                if mode.strict or false then
                  v
                else
                  throw "gen-rules.defunctionalize: ${mode.where or ""} at ${builtins.toJSON pos}: ${why}; write the closure at an aspect position (`includes`), with the property on the definition it ranks there";
              lifts = [ ];
              found = [ ];
              bad = [ { inherit pos why; } ];
            }
          else
            combine ws
            // {
              value =
                if v._type == "merge" then
                  v // { contents = map (w: w.value) ws; }
                else
                  v // { content = (head ws).value; };
              lifts =
                if v._type == "if" then map (l: l // { wrap = x: v // { content = l.wrap x; }; }) lifts else lifts;
            }
        else
          classLeafAt pos v;

      classLeafAt =
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
          lifts =
            if liftable then
              [
                {
                  inherit pos coords;
                  fn = v;
                  wrap = x: x;
                }
              ]
            else
              [ ];
          found = [ ];
          bad = if refused then [ { inherit pos why; } ] else [ ];
        };

      # `{ <class> = f; }`, f over coordinates C and module args M, becomes the aspect-position closure
      # `{ C }: { <class>.imports = [ <f with C applied, M kept> ]; }` (gate v2 G3): a door node in
      # `includes`. The class value is aspect content whatever formals remain, so a coordinate-only f
      # (M empty, not a module function of `cnf.moduleArgs` [gate v1 Q7]) lifts as any other does. A
      # class-key `mkIf` the closure was written under wraps the class value (`l.wrap`, den-hoag-crk5e).
      liftOf =
        k: l:
        let
          margs = removeAttrs (functionArgs l.fn) l.coords;
        in
        {
          __functionArgs = genAttrs l.coords (_: false);
          __functor = _: ctx: {
            ${k} = l.wrap {
              imports = [
                {
                  __functionArgs = margs;
                  __functor = _: m: l.fn (m // genAttrs l.coords (n: ctx.${n}));
                }
              ];
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
            if elem k tableKeys then
              # S1 (a): the framework-mounted registration table inside an aspect: carried, never
              # entered (its closures are registrations already).
              leaf c
            else if k == "includes" then
              includesAt (pos ++ [ k ]) c
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
          liftWalks = builtins.concatMap (k: map (l: closureAt l.pos (liftOf k l)) ws.${k}.lifts) classKeys;
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
                      # a wrapped `includes` (`mkIf c [ … ]`): the lifted nodes land as their own,
                      # unconditional definition beside it
                      merge.mkMerge [
                        base
                        extra
                      ];
                }
            );
        };
    in
    {
      inherit
        aspectAt
        collectionAt
        listAt
        wrapperAt
        ;
    };
in
{
  inherit
    walk
    addressKey
    prefixKeys
    viewOf
    tableAt
    tableAtOf
    registrations
    mountKey
    mountsOf
    patternOf
    conditionOf
    isCallable
    leaf
    combine
    wrapperAt
    ;
}
