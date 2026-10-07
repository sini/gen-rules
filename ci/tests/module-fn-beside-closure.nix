# S1 beside a closure (den-hoag-cgobz): a module function `y` written at the same aspect key as a
# context closure `x`. gen-rules lowers `x` into a door node, a guard record, so `main` is a guard
# carrier; gen-aspects applies `y` once, in the one evaluation, in its own `includes` element (the T4
# home, as beside a plain definition), and the carrier holds that element in a `coerced` fragment.
# `viewOf` reads a carrier as a node whose own table is empty and whose `includes` are its coerced
# elements, so the closure in `y`'s result registers in its element's table and the door finds it.
#
# RED (measured at gen-rules 8ebc889, gen-aspects 6c9ea4e): `y` was held raw, registrations read 1 of
# 2 and firing `main` handed the raw function onward.
{
  genRules,
  genAlgebra,
  genIdentity,
  genAspects,
  genProgram,
  genMerge,
  ...
}@args:
let
  m = import ./_fixtures/mounted.nix args;
  inherit (m) inner ctx;
  merge = genMerge;
  F = modules: m.framework { inherit modules; };
  regs = mods: builtins.length (m.registered (F mods).r.config.lambdas);
  # a framework aspect module adding an include to the aspect named `main`, mounted beside `lambdasMount`
  regsWith =
    extra: modules:
    builtins.length (m.registered (m.framework { inherit modules extra; }).r.config.lambdas);
  addCommon = { name, ... }: {
    includes = merge.mkIf (name == "main") [ { description = "COMMON"; } ];
  };
  # Fire `main`, then every door node in its output, descending into include elements.
  served =
    mods:
    let
      f = F mods;
      a = f.r.config.aspects.main;
      o = if m.isGuard a then f.fire ctx a else a;
      walkOut =
        v:
        builtins.concatMap (
          e:
          if m.isGuard e then
            let
              r = f.fire ctx e;
            in
            [ (r.description or "?") ] ++ walkOut r
          else if builtins.isAttrs e then
            (if e ? description then [ e.description ] else [ ]) ++ walkOut e
          else if builtins.isFunction e then
            [ "<raw-function>" ]
          else
            [ "?" ]
        ) (v.includes or [ ]);
    in
    [ (o.description or "-") ] ++ walkOut o;
  x = {
    key = "x";
    config.aspects.main = { thimble, ... }: { description = "G-${thimble}"; };
  };
  y = {
    key = "y";
    config.aspects.main = { config, ... }: { includes = [ inner ]; };
  };
  yPlain = {
    key = "y";
    config.aspects.main.includes = [ inner ];
  };
  y2 = {
    key = "y2";
    config.aspects.main = { config, ... }: {
      includes = [ ({ bobbin, ... }: { description = "B-${bobbin}"; }) ];
    };
  };
  yThrow = {
    key = "y";
    config.aspects.main = { config, ... }: throw "y applied";
  };
  # `y`'s include conditioned on a read of the evaluation's own config
  yCond = c: {
    key = "y";
    imports = [
      (
        { config, ... }@top:
        {
          config.aspects.main = { config, ... }: { includes = merge.mkIf (c top.config) [ inner ]; };
        }
      )
    ];
  };
  carrierOf = f: f.r.config.aspects.main;
  xRecord =
    f: (builtins.head (builtins.filter (fr: fr.kind == "record") (carrierOf f).fragments)).guard;
  fireX =
    mods:
    let
      f = F mods;
    in
    (f.fire ctx (xRecord f)).description;
  # fire `main`'s own closure `x` from inside the evaluation, through the root table and the door
  firesXIn =
    cfg:
    let
      cnf = {
        entityKinds = null;
        keySemantics.nixos.category = "class";
        inherit (m.w) moduleArgs;
        aspectModules = [ (genRules.lambdasMount "lambdas") ];
      };
      door = genRules.mkApply {
        lambdas = cfg.lambdas;
        inherit cnf;
        declared = null;
      };
      vocab = genAspects.mkGuardVocab (cnf // { ref = door; });
      g = (builtins.head (builtins.filter (fr: fr.kind == "record") cfg.aspects.main.fragments)).guard;
    in
    vocab.applyGuardWith {
      context = ctx;
      sources = m.srcs;
      scope = { };
    } g != null;
  t4 = [
    "G-x"
    "Aspect [definition 1-entry 1]"
    "T-x"
  ];
  # den-hoag-3849t: every description reached from `main`, firing each door node met at an aspect
  # position, an `includes` element or a nested key; a raw function there is "<raw-function>"
  render =
    f: v:
    if m.isGuard v then
      let
        r = f.fire ctx v;
      in
      if r == null then [ "<not-fired>" ] else render f r
    else if builtins.isFunction v then
      [ "<raw-function>" ]
    else if builtins.isAttrs v then
      (if v ? description then [ v.description ] else [ ])
      ++ builtins.concatMap (render f) (if builtins.isList (v.includes or null) then v.includes else [ ])
      ++ builtins.concatMap (k: render f v.${k}) (
        builtins.filter (
          k:
          !(builtins.elem k [
            "includes"
            "lambdas"
            "description"
            "meta"
            "name"
            "key"
            "id_hash"
            "nixos"
            "__guard"
            "fragments"
            "__functor"
            "__functionArgs"
          ])
          && (builtins.isAttrs v.${k} || builtins.isFunction v.${k})
        ) (builtins.attrNames v)
      )
    else
      [ "?" ];
  servedAll =
    mods:
    let
      f = F mods;
    in
    render f f.r.config.aspects.main;
  firedMain =
    mods:
    let
      f = F mods;
    in
    f.fire ctx f.r.config.aspects.main;
  fn = { config, ... }: { includes = [ inner ]; };
  plain = k: v: {
    key = "plain-${k}";
    config.aspects.main = v;
  };
  q = d: { description = d; };
  # a closure at `main` whose fired record writes `e thimble` beside its description; its T4 twin
  xsW = e: {
    key = "xs";
    config.aspects.main = { thimble, ... }: { description = "G-${thimble}"; } // e thimble;
  };
  t4W = e: {
    key = "xs";
    config.aspects.main = {
      description = "P";
    }
    // e "x";
  };
  besideX = v: [
    x
    (plain "z" v)
  ];
  regsServed = mods: {
    registrations = regs mods;
    served = servedAll mods;
  };
  appliedRow = {
    registrations = 2;
    served = t4;
  };
  # den-hoag-dmdou: `other` is a carrier (`x` and a module function), and `main` carries it by value
  yAt = at: {
    key = "y-${at}";
    config.aspects.${at} = { config, ... }: {
      description = "Y";
      includes = [ inner ];
    };
  };
  otherCarrier = [
    {
      key = "x-other";
      config.aspects.other = { thimble, ... }: { description = "G-${thimble}"; };
    }
    (yAt "other")
  ];
  ref = how: {
    key = "ref";
    imports = [
      (
        { config, ... }@top:
        {
          config.aspects.main =
            if how == "includes" then
              { includes = [ top.config.aspects.other ]; }
            else if how == "value" then
              top.config.aspects.other
            else
              { sub = top.config.aspects.other; };
        }
      )
    ];
  };
in
{
  flake.tests.module-fn-beside-closure = {
    # G1: both closures register; the control writes `inner` plainly
    test-g1-closure-and-module-function-register-both = {
      expr = {
        carrier = regs [
          x
          y
        ];
        control = regs [
          x
          yPlain
        ];
      };
      expected = {
        carrier = 2;
        control = 2;
      };
    };

    # G2: firing `main` serves `x`'s text and, through `y`'s applied element, `inner`'s
    test-g2-firing-the-carrier-serves-both = {
      expr = {
        carrier = served [
          x
          y
        ];
        control = served [
          x
          yPlain
        ];
      };
      expected = {
        carrier = t4;
        control = [
          "G-x"
          "T-x"
        ];
      };
    };

    # G3: two module functions beside the closure, each in its own element
    test-g3-two-module-functions-register-each = {
      expr = {
        registrations = regs [
          x
          y
          y2
        ];
        served = served [
          x
          y
          y2
        ];
      };
      expected = {
        registrations = 3;
        served = t4 ++ [
          "Aspect [definition 2-entry 1]"
          "B-b"
        ];
      };
    };

    # G8: an aspect module's own `includes` contribution does not displace the carrier's elements
    test-g8-framework-include-leaves-the-carriers-elements = {
      expr = {
        carrier =
          regsWith
            [ addCommon ]
            [
              x
              y
            ];
        control =
          regsWith
            [ addCommon ]
            [
              x
              yPlain
            ];
      };
      expected = {
        carrier = 2;
        control = 2;
      };
    };

    # G4: the carrier one level down, at a nested key
    test-g4-nested-key-carrier-registers-both = {
      expr = regs [
        {
          key = "xs";
          config.aspects.main.sub = { thimble, ... }: { description = "GS-${thimble}"; };
        }
        {
          key = "ys";
          config.aspects.main.sub = { config, ... }: { includes = [ inner ]; };
        }
      ];
      expected = 2;
    };

    # G6: firing `x` reads the carrier's own table, which is empty, so `y` is never applied
    test-g6-firing-the-closure-does-not-apply-the-module-function = {
      expr = {
        beside = fireX [
          x
          yThrow
        ];
        control = fireX [
          x
          y
        ];
      };
      expected = {
        beside = "G-x";
        control = "G-x";
      };
    };

    # G7 (the 1wdng class): `y`'s include is conditioned on firing `main`'s own closure `x` through
    # the root table and the door, in the same evaluation
    test-g7-condition-firing-the-carriers-own-closure-is-served = {
      expr = {
        fires = served [
          x
          (yCond firesXIn)
        ];
        control = served [
          x
          (yCond (_: true))
        ];
      };
      expected = {
        fires = t4;
        control = t4;
      };
    };

    # den-hoag-3849t. A module function at an aspect position of a plain definition beside `x` is
    # applied where F4(b)'s coercion puts it: in an `includes` element, a nested key's function coerced
    # into that key's `includes`. RED (gen-rules 0b13703, gen-aspects 36b3879): registrations 1 and the
    # raw function served.
    # H1: `main.sub = fn`
    test-h1-a-module-function-at-a-nested-key-is-applied = {
      expr = regsServed (besideX {
        sub = fn;
      });
      expected = appliedRow;
    };

    # H2: `main.includes = [ fn ]`
    test-h2-a-module-function-in-a-plain-include-is-applied = {
      expr = regsServed (besideX {
        includes = [ fn ];
      });
      expected = appliedRow;
    };

    # H3: below an include element, below a nested key's `includes`, and two keys down
    test-h3-a-module-function-deeper-in-a-plain-definition-is-applied = {
      expr = {
        elemIncludes = regsServed (besideX {
          includes = [ { includes = [ fn ]; } ];
        });
        nestedIncludes = regsServed (besideX {
          sub.includes = [ fn ];
        });
        deepNested = regsServed (besideX {
          sub.sub2 = fn;
        });
      };
      expected = {
        elemIncludes = {
          registrations = 2;
          served = [
            "G-x"
            "Aspect [definition 1-entry 1]"
            "Aspect [definition 1-entry 1]"
            "T-x"
          ];
        };
        nestedIncludes = appliedRow;
        deepNested = appliedRow;
      };
    };

    # H4 (NON-REGRESSION: base serves the same; its discriminator is a construction that types nested
    # positions as aspects, whose default `description` conflicts with the fired one): a fired nested
    # scalar beside a plain nested include
    test-h4-a-fired-nested-scalar-beside-a-plain-nested-include-is-served = {
      expr = servedAll [
        (xsW (t: {
          sub.description = "R-${t}";
        }))
        (plain "si" { sub.includes = [ (q "Q") ]; })
      ];
      expected = [
        "G-x"
        "R-x"
        "Q"
      ];
    };

    # H5: the same fired nested scalar beside `main.sub = fn` (RED: registrations 1, served THROWS)
    test-h5-a-fired-nested-scalar-beside-a-nested-module-function = {
      expr = regsServed [
        (xsW (t: {
          sub.description = "R-${t}";
        }))
        (plain "sf" { sub = fn; })
      ];
      expected = {
        registrations = 2;
        served = [
          "G-x"
          "R-x"
          "Aspect [definition 1-entry 1]"
          "T-x"
        ];
      };
    };

    # H6 (NON-REGRESSION, as H4): the fired nested aspect carries only what was written
    test-h6-the-fired-nested-aspect-keys-are-what-was-written = {
      expr =
        builtins.attrNames
          (firedMain [
            (xsW (t: {
              sub.description = "R-${t}";
            }))
            (plain "si" { sub.includes = [ (q "Q") ]; })
          ]).sub;
      expected = [
        "description"
        "includes"
      ];
    };

    # H7: a plain include is served once (the typed list), not again from the raw remainder
    test-h7-a-plain-include-is-served-once = {
      expr = {
        served = servedAll (besideX {
          includes = [ (q "Q") ];
        });
        includes =
          builtins.length
            (firedMain (besideX {
              includes = [ (q "Q") ];
            })).includes;
      };
      expected = {
        served = [
          "G-x"
          "Q"
        ];
        includes = 1;
      };
    };

    # H8: a plain `includes = mkIf true [ Q ]` is discharged to a list (RED: the property marker handed
    # onward, keys `_type`/`condition`/`content`, and `Q` dropped)
    test-h8-a-conditional-plain-include-is-discharged = {
      expr =
        let
          mods = besideX { includes = merge.mkIf true [ (q "Q") ]; };
          i = (firedMain mods).includes;
        in
        {
          includes = if builtins.isAttrs i then builtins.attrNames i else builtins.length i;
          served = servedAll mods;
        };
      expected = {
        includes = 1;
        served = [
          "G-x"
          "Q"
        ];
      };
    };

    # H9: two scalars, the fired one and a plain one, stay refused by F4(a)'s content law
    test-h9-a-plain-scalar-beside-the-fired-one-stays-refused = {
      expr =
        (builtins.tryEval (
          builtins.deepSeq (servedAll [
            x
            (plain "p" { description = "P"; })
          ]) null
        )).success;
      expected = false;
    };

    # K1: a nested value under a property (`mkIf`, `mkMerge`, `mkOrder`) is projected through, its
    # wrapper kept, so the typed child discharges it as T4 would. RED: registrations 1, raw function.
    # An override (`mkForce`) over a typed position at a nested key is refused by name instead
    # (den-hoag-15wnx, gen-aspects' stated shortfall): its message is ci/tests-error.nix
    # `test-k1-an-override-over-a-nested-typed-position-is-refused-by-name`.
    test-k1-a-module-function-under-a-property-at-a-nested-key-is-applied = {
      expr = {
        mkIf = regsServed (besideX {
          sub = merge.mkIf true { includes = [ fn ]; };
        });
        mkIfFn = regsServed (besideX {
          sub = merge.mkIf true fn;
        });
        mkMerge = regsServed (besideX {
          sub = merge.mkMerge [
            { includes = [ fn ]; }
            { description = "S"; }
          ];
        });
        mkOrder = regsServed (besideX {
          sub = merge.mkOrder 500 { includes = [ fn ]; };
        });
      };
      expected = {
        mkIf = appliedRow;
        mkIfFn = appliedRow;
        # the `mkMerge`'s raw member (`description = "S"`) is discharged and served at `sub`, as the module
        # system serves it (den-hoag-15wnx); before, the marker was carried as data and `S` was not reached
        mkMerge = appliedRow // {
          served = [
            "G-x"
            "S"
            "Aspect [definition 1-entry 1]"
            "T-x"
          ];
        };
        mkOrder = appliedRow;
      };
    };

    # den-hoag-15wnx: a property over raw content at a nested key of a plain definition is discharged
    # by the carrier's content law, beside the fired record's own nested content, as T4 discharges it.
    # n4f (`mkIf false`, nothing beside it) is ci/tests-error.nix; n4m is K1's `mkMerge` arm.
    # n10f: `mkIf false` beside the fired `sub` drops `S` (RED: `S` served)
    test-n10f-a-false-conditional-beside-fired-nested-content-is-dropped = {
      expr =
        let
          e = t: { sub.description = "R-${t}"; };
          p = plain "n10f" { sub = merge.mkIf false { description = "S"; }; };
        in
        {
          carrier = servedAll [
            (xsW e)
            p
          ];
          t4 = servedAll [
            (t4W e)
            p
          ];
        };
      expected = {
        carrier = [
          "G-x"
          "R-x"
        ];
        t4 = [
          "P"
          "R-x"
        ];
      };
    };

    # n9r: `mkForce` over raw content beats the fired `sub` (RED: both served, the override ignored)
    test-n9r-an-override-over-raw-nested-content-beats-the-fired-content = {
      expr =
        let
          e = t: { sub.description = "R-${t}"; };
          p = plain "n9r" { sub = merge.mkForce { description = "S"; }; };
        in
        {
          carrier = servedAll [
            (xsW e)
            p
          ];
          t4 = servedAll [
            (t4W e)
            p
          ];
        };
      expected = {
        carrier = [
          "G-x"
          "S"
        ];
        t4 = [
          "P"
          "S"
        ];
      };
    };

    # n10t: `mkIf true` as the only definition of `sub`; the fired `sub` holds the content, not the
    # marker (RED: keys `_type`/`condition`/`content`; `render` descends into `content`, so read keys)
    test-n10t-a-true-conditional-at-a-nested-key-is-discharged = {
      expr =
        builtins.attrNames
          (firedMain (besideX {
            sub = merge.mkIf true { description = "S"; };
          })).sub;
      expected = [ "description" ];
    };

    # Include order: the typed positions are one fragment, placed at the first definition that is not
    # the fired record, so plain includes precede the fired record's; T4 keeps definition order.
    test-the-include-order-against-t4 = {
      expr = {
        carrier = servedAll [
          (plain "a" { includes = [ (q "A") ]; })
          (xsW (t: {
            includes = [ (q "X-${t}") ];
          }))
          (plain "b" { includes = [ (q "B") ]; })
        ];
        t4 = servedAll [
          (plain "a" { includes = [ (q "A") ]; })
          (t4W (t: {
            includes = [ (q "X-${t}") ];
          }))
          (plain "b" { includes = [ (q "B") ]; })
        ];
      };
      expected = {
        carrier = [
          "G-x"
          "A"
          "B"
          "X-x"
        ];
        t4 = [
          "P"
          "A"
          "X-x"
          "B"
        ];
      };
    };

    # den-hoag-dmdou. A carrier carried by value is served where it is placed. RED (gen-rules 0b13703,
    # gen-aspects 36b3879): every row aborted uncatchably, `attribute 'condition' missing`.
    # D1: as an include element
    test-d1-a-carrier-included-by-value-is-served = {
      expr = regsServed (otherCarrier ++ [ (ref "includes") ]);
      expected = {
        registrations = 2;
        served = [
          "Aspect main"
          "G-x"
          "Y"
          "T-x"
        ];
      };
    };

    # D2: beside a module function at `main`, the element's own closures looked up through its view
    test-d2-a-carrier-included-beside-a-module-function-is-served = {
      expr = servedAll (
        otherCarrier
        ++ [
          (ref "includes")
          {
            key = "mainFn";
            config.aspects.main =
              { config, ... }:
              {
                includes = [ ({ bobbin, ... }: { description = "M-${bobbin}"; }) ];
              };
          }
        ]
      );
      expected = [
        "Aspect main"
        "Aspect [definition 1-entry 1]"
        "M-b"
        "G-x"
        "Y"
        "T-x"
      ];
    };

    # D3: as the whole aspect, and at a nested key
    test-d3-a-carrier-as-the-aspect-or-at-a-nested-key-is-served = {
      expr = {
        value = servedAll (otherCarrier ++ [ (ref "value") ]);
        sub = servedAll (otherCarrier ++ [ (ref "sub") ]);
      };
      expected = {
        value = [
          "G-x"
          "Y"
          "T-x"
        ];
        sub = [
          "Aspect main"
          "G-x"
          "Y"
          "T-x"
        ];
      };
    };

    # D4: as one of several definitions, its fragments spliced
    test-d4-a-carrier-beside-a-plain-definition-is-spliced = {
      expr = servedAll (
        otherCarrier
        ++ [
          (ref "value")
          (plain "q" { includes = [ (q "Q") ]; })
        ]
      );
      expected = [
        "G-x"
        "Y"
        "T-x"
        "Q"
      ];
    };
  };
}
