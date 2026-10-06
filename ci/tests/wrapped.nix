# den-hoag-crk5e: a closure under one of the module system's property wrappers is lowered exactly as the
# same closure unwrapped, at every position the one lowering walks (design Section 3 (b): "It passes
# through the module system's property wrappers … and lowers their contents, never their conditions").
# The wrapper class is gen-merge's own: the four `_type`s `priority.nix` constructs (`if`, `merge`,
# `override`, `order`), reached through every constructor it exports.
#
#   includes   a wrapped `includes` definition (`attrsAt` hands it to its own step)
#   above      a wrapper above a declared aspect or rule path (`descend`)
#   class      a wrapped closure at a class key: lifted, its `mkIf` riding on the class value in the node
#   door       a wrapper in the door's output: the scope position is an address into the output
#   semantics  priority and order are gen-merge's, read off plain elements as the control
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
  inherit (m)
    w
    inner
    run
    framework
    ctx
    guardsIn
    classMarker
    ;
  merge = genMerge;
  inner2 = { bobbin, ... }: { description = "B-${bobbin}"; };
  has = n: w.T.term.all [ (w.T.term.has n) ];
  served = {
    registrations = 1;
    conditions = [ (has "thimble") ];
    fired = [ { description = "T-x"; } ];
  };
  one = mod: run { modules = [ mod ]; };
  inc = v: { aspects.main.includes = v; };
  regs = mods: builtins.length (builtins.attrNames (framework { modules = mods; }).r.config.lambdas);
  descs = mods: map (x: x.description) (framework { modules = mods; }).r.config.aspects.main.includes;
  firedDescs = mods: map (o: o.description) (run { modules = mods; }).fired;
  held = mod: classMarker (framework { modules = [ mod ]; }).r.config.aspects.main.nixos;
  # the door's output, written by a closure at `includes`, read through its wrapper
  doorOut =
    out:
    let
      f = framework { modules = [ (inc [ ({ thimble, ... }: out) ]) ]; };
      o = f.fire ctx (builtins.head (guardsIn f.r.config.aspects.main));
      body = if o ? _type then o.content or (builtins.head o.contents) else o;
      list = if body.includes ? _type then body.includes.content else body.includes;
    in
    # the door fires the nested nodes it reaches through the scope positions; one it did not reach
    # stays a guard
    map (x: if m.isGuard x then "unreached" else x.description) list;
  coordClass = { bobbin, pkgs, ... }: { marker = "delivered"; };
  # a fired node's class value read as gen-aspects' class option reads it (`nullOr deferredModule`,
  # which discharges a class-key `mkIf` on the definition), then its marker; `none` when it delivers
  # nothing
  asClass =
    v:
    let
      c =
        (merge.evalModuleTree { } [
          {
            options.c = merge.mkOption {
              type = merge.types.nullOr merge.types.deferredModule;
              default = null;
            };
          }
          { config.c = v; }
        ]).config.c;
    in
    if c == null then "none" else classMarker c;
  oneClass =
    mod:
    let
      f = framework { modules = [ mod ]; };
      nodes = guardsIn f.r.config.aspects.main;
      out = o: if o ? nixos then { nixos = asClass o.nixos; } else o;
    in
    {
      registrations = builtins.length (builtins.attrNames f.r.config.lambdas);
      conditions = map (n: n.condition) nodes;
      fired = map (n: out (f.fire ctx n)) nodes;
    };
in
{
  flake.tests.wrapped-closures = {
    test-includes-under-every-wrapper-is-lowered-as-unwrapped = {
      expr = {
        plain = one (inc [ inner ]);
        mkIf = one (inc (merge.mkIf true [ inner ]));
        mkMerge = one (inc (merge.mkMerge [ [ inner ] ]));
        mkOverride = one (inc (merge.mkOverride 70 [ inner ]));
        mkForce = one (inc (merge.mkForce [ inner ]));
        mkDefault = one (inc (merge.mkDefault [ inner ]));
        mkOptionDefault = one (inc (merge.mkOptionDefault [ inner ]));
        mkOrder = one (inc (merge.mkOrder 700 [ inner ]));
        mkBefore = one (inc (merge.mkBefore [ inner ]));
        mkAfter = one (inc (merge.mkAfter [ inner ]));
        nested = one (inc (merge.mkIf true (merge.mkMerge [ (merge.mkBefore [ inner ]) ])));
      };
      expected = {
        plain = served;
        mkIf = served;
        mkMerge = served;
        mkOverride = served;
        mkForce = served;
        mkDefault = served;
        mkOptionDefault = served;
        mkOrder = served;
        mkBefore = served;
        mkAfter = served;
        nested = served;
      };
    };

    test-a-false-condition-registers-and-delivers-nothing = {
      expr = {
        includes = one (inc (merge.mkIf false [ inner ]));
        # the reference: the same wrapper at the aspect position, lowered before this row
        aspect = regs [
          {
            aspects.main = merge.mkMerge [
              (merge.mkIf false { includes = [ inner ]; })
              { }
            ];
          }
        ];
      };
      expected = {
        includes = {
          registrations = 1;
          conditions = [ ];
          fired = [ ];
        };
        aspect = 1;
      };
    };

    # contents lowered, never conditions: the loader's own output (no module evaluation, which discharges
    # `includes` and so reads its conditions) registers each closure with its condition a throw
    test-the-lowering-never-forces-a-condition =
      let
        lowerRegs =
          mod:
          let
            lowered =
              builtins.elemAt
                (genRules.defunctionalize {
                  cnf = w.cnfOf w.D;
                  declared = w.D;
                  key = "lz";
                  lambdasPath = [ "lambdas" ];
                  aspectPaths = [ [ "aspects" ] ];
                } mod).imports
                0;
          in
          builtins.length (builtins.attrNames (builtins.elemAt lowered.config.contents 1).lambdas);
        never = throw "condition forced";
      in
      {
        expr = {
          includes = lowerRegs { config.aspects.main.includes = merge.mkIf never [ inner ]; };
          above = lowerRegs { config = merge.mkIf never { aspects.main.includes = [ inner ]; }; };
          class = lowerRegs { config.aspects.main.nixos = merge.mkIf never ({ bobbin, pkgs, ... }: { }); };
        };
        expected = {
          includes = 1;
          above = 1;
          class = 1;
        };
      };

    test-priority-and-order-stay-gen-merges = {
      expr = {
        after = firedDescs [
          (inc (
            merge.mkMerge [
              (merge.mkAfter [ inner ])
              [ inner2 ]
            ]
          ))
        ];
        afterControl = descs [
          (inc (
            merge.mkMerge [
              (merge.mkAfter [ { description = "A"; } ])
              [ { description = "B"; } ]
            ]
          ))
        ];
        force = firedDescs [
          (inc (
            merge.mkMerge [
              (merge.mkForce [ inner ])
              [ inner2 ]
            ]
          ))
        ];
        forceControl = descs [
          (inc (
            merge.mkMerge [
              (merge.mkForce [ { description = "F"; } ])
              [ { description = "P"; } ]
            ]
          ))
        ];
        forceRegistrations = regs [
          (inc (
            merge.mkMerge [
              (merge.mkForce [ inner ])
              [ inner2 ]
            ]
          ))
        ];
      };
      expected = {
        after = [
          "B-b"
          "T-x"
        ];
        afterControl = [
          "B"
          "A"
        ];
        force = [ "T-x" ];
        forceControl = [ "F" ];
        forceRegistrations = 2;
      };
    };

    test-a-wrapper-above-the-declared-path-is-lowered-through = {
      expr = {
        config = one { config = merge.mkIf true { aspects.main.includes = [ inner ]; }; };
        configForce = one { config = merge.mkForce { aspects.main.includes = [ inner ]; }; };
        # two contents of one mkMerge lower at two positions, so two different closures are two ids
        configMerge = firedDescs [
          {
            config = merge.mkMerge [
              { aspects.main.includes = [ inner ]; }
              { aspects.main.includes = [ inner2 ]; }
            ];
          }
        ];
        configMergeControl = descs [
          {
            config = merge.mkMerge [
              { aspects.main.includes = [ { description = "A"; } ]; }
              { aspects.main.includes = [ { description = "B"; } ]; }
            ];
          }
        ];
        configFalse = regs [ { config = merge.mkIf false { aspects.main.includes = [ inner ]; }; } ];
        rule =
          let
            f = w.framework {
              modules = [ { config = merge.mkIf true { fw.rules.r1 = { thimble, ... }: [ ]; }; } ];
            };
          in
          {
            registrations = builtins.length (builtins.attrNames f.config.lambdas);
            doorRule = f.config.rules.r1 ? when;
          };
      };
      expected = {
        config = served;
        configForce = served;
        configMerge = [
          "B-b"
          "T-x"
        ];
        configMergeControl = [
          "B"
          "A"
        ];
        configFalse = 1;
        rule = {
          registrations = 1;
          doorRule = true;
        };
      };
    };

    test-a-wrapped-class-key-closure-is-lifted-with-its-condition = {
      expr = {
        plain = oneClass { aspects.main.nixos = coordClass; };
        mkIf = oneClass { aspects.main.nixos = merge.mkIf true coordClass; };
        mkIfHeld = held { aspects.main.nixos = merge.mkIf true coordClass; };
        mkIfFalse = oneClass { aspects.main.nixos = merge.mkIf false coordClass; };
        mkIfNested = oneClass { aspects.main.nixos = merge.mkIf true (merge.mkIf false coordClass); };
        mkMerge = oneClass {
          aspects.main.nixos = merge.mkMerge [
            coordClass
            ({ pkgs, ... }: { })
          ];
        };
        # beside a wrapped `includes`, the lift lands as its own `includes` definition
        withWrappedIncludes = oneClass {
          aspects.main = {
            includes = merge.mkIf true [ inner ];
            nixos = coordClass;
          };
        };
        # a MODULE function under a wrapper stays a module slot, delivered as written
        moduleFnIf = held {
          aspects.main.nixos = merge.mkIf true ({ pkgs, ... }: { marker = "m-${pkgs}"; });
        };
        moduleFnForce = held { aspects.main.nixos = merge.mkForce ({ pkgs, ... }: { marker = "f"; }); };
      };
      expected =
        let
          lifted = {
            registrations = 1;
            conditions = [ (has "bobbin") ];
            fired = [ { nixos = "delivered"; } ];
          };
        in
        {
          plain = lifted;
          mkIf = lifted;
          mkIfHeld = "none";
          # the node is registered and fires; the condition, on the class value it carries, delivers
          # nothing
          mkIfFalse = lifted // {
            fired = [ { nixos = "none"; } ];
          };
          mkIfNested = lifted // {
            fired = [ { nixos = "none"; } ];
          };
          mkMerge = lifted;
          withWrappedIncludes = {
            registrations = 2;
            conditions = [
              (has "thimble")
              (has "bobbin")
            ];
            fired = [
              { description = "T-x"; }
              { nixos = "delivered"; }
            ];
          };
          moduleFnIf = "m-P";
          moduleFnForce = "f";
        };
    };

    # den-hoag-crk5e gate C1: the lift adds no strictness (design Section 3 (b)). A class-key condition
    # rides on the class value inside the lifted node, never on its `includes` entry, so neither reading
    # the aspect's `includes` (this lift's own surface) nor reading the root table (the S1 (a) union,
    # which reads every aspect's `includes`) forces it.
    test-a-class-key-condition-is-not-forced-by-reading-includes-or-the-table =
      let
        mod = {
          aspects.main.nixos = merge.mkIf (throw "class-key condition forced") coordClass;
        };
        f = framework { modules = [ mod ]; };
      in
      {
        expr = {
          includes = builtins.length f.r.config.aspects.main.includes;
          table = builtins.length (builtins.attrNames f.r.config.lambdas);
        };
        expected = {
          includes = 1;
          table = 1;
        };
      };

    test-a-wrapper-in-the-door-output-is-an-address = {
      expr = {
        plain = doorOut { includes = [ inner2 ]; };
        includesIf = doorOut { includes = merge.mkIf true [ inner2 ]; };
        wholeIf = doorOut (merge.mkIf true { includes = [ inner2 ]; });
        wholeMerge = doorOut (merge.mkMerge [ { includes = [ inner2 ]; } ]);
        # `order` steps `"content"` too, a step gen-merge's `dischargePropertiesAt` does not take
        includesBefore = doorOut { includes = merge.mkBefore [ inner2 ]; };
        includesForce = doorOut { includes = merge.mkForce [ inner2 ]; };
        wholeForce = doorOut (merge.mkForce { includes = [ inner2 ]; });
      };
      expected = {
        plain = [ "B-b" ];
        includesIf = [ "B-b" ];
        wholeIf = [ "B-b" ];
        wholeMerge = [ "B-b" ];
        includesBefore = [ "B-b" ];
        includesForce = [ "B-b" ];
        wholeForce = [ "B-b" ];
      };
    };
  };
}
