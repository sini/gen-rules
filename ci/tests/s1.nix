# S1, ruled arm (a) (den-hoag-lwbb1, sitting den-hoag-rwuqw, 2026-10-05): a closure inside the result of a
# module function written at an aspect position (`main = { config, ... }: { … }`) registers when the
# module system applies the function, because the framework mounts gen-rules' `lambdas` inside
# gen-aspects' aspect submodule (`lambdasMount` in `cnf.aspectModules`), the one cnf the loader and the
# door read. Every aspect's table is a definition of the root table, so the module system's own merge
# unites them and refuses a duplicate id by name. These cells read the loader over gen-aspects'
# REAL aspect schema and fire through the door:
#
#   s1a  a closure at `includes` inside the module function: served, as its control is.
#   s1c  a closure over a coordinate at a CLASS KEY inside the module function: lifted with its `has`
#        guard, the same condition as its control. Fired with a module-argument formal, it delivers;
#        a coordinate-only one fires too (`module-fn-shapes.nix`, den-hoag-d13lv).
#   s1e  the same with a body reading the coordinate: at a context without it, the door node does not
#        fire under a declared set and the door refuses by name under the open world; never gen-merge.
#
# Each carries its control: the same text OUTSIDE the module function, lowered at load.
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
  inherit (m.w) R merge aspects;
  keySemantics.nixos.category = "class";
  inherit (m)
    w
    D
    src
    ctx
    srcs
    inner
    at
    framework
    isGuard
    guardsIn
    classMarker
    out
    run
    ids
    A
    B
    C
    Am
    shared
    pinnedVsControl
    ;
in
{
  flake.tests.s1-framework-mounted-lambdas = {
    test-s1a-closure-in-includes-inside-a-module-function-is-served = {
      expr =
        pinnedVsControl { modules = [ { aspects.main = { config, ... }: { includes = [ inner ]; }; } ]; }
          {
            modules = [ { aspects.main.includes = [ inner ]; } ];
          };
      expected =
        let
          v = {
            registrations = 1;
            conditions = [ (w.T.term.all [ (w.T.term.has "thimble") ]) ];
            fired = [ { description = "T-x"; } ];
          };
        in
        {
          pinned = v;
          control = v;
        };
    };

    test-s1c-class-key-closure-inside-a-module-function-keeps-its-guard = {
      expr = {
        # coordinate-only: the condition (its firing is read in module-fn-shapes.nix)
        condition =
          (run { modules = [ { aspects.main = { config, ... }: { nixos = { bobbin, ... }: { }; }; } ]; })
          .conditions;
        conditionControl =
          (run { modules = [ { aspects.main.nixos = { bobbin, ... }: { }; } ]; }).conditions;
        # with a module-argument formal: delivered when `bobbin` is present, not fired when absent
        # under the declared set
        served = pinnedVsControl {
          modules = [ { aspects.main = { config, ... }: { nixos = { bobbin, pkgs, ... }: { }; }; } ];
        } { modules = [ { aspects.main.nixos = { bobbin, pkgs, ... }: { }; } ]; };
        absentClosed =
          pinnedVsControl
            {
              modules = [ { aspects.main = { config, ... }: { nixos = { bobbin, pkgs, ... }: { }; }; } ];
              closed = true;
              context.thimble = "x";
            }
            {
              modules = [ { aspects.main.nixos = { bobbin, pkgs, ... }: { }; } ];
              closed = true;
              context.thimble = "x";
            };
      };
      expected =
        let
          has = [ (w.T.term.all [ (w.T.term.has "bobbin") ]) ];
        in
        {
          condition = has;
          conditionControl = has;
          served = {
            pinned = {
              registrations = 1;
              conditions = has;
              fired = [ { nixos = "none"; } ];
            };
            control = {
              registrations = 1;
              conditions = has;
              fired = [ { nixos = "none"; } ];
            };
          };
          absentClosed = {
            pinned = {
              registrations = 1;
              conditions = has;
              fired = [ "not-fired" ];
            };
            control = {
              registrations = 1;
              conditions = has;
              fired = [ "not-fired" ];
            };
          };
        };
    };

    test-s1e-class-key-closure-reading-its-coordinate-reaches-the-door = {
      expr =
        let
          s1e = { config, ... }: { nixos = { bobbin, pkgs, ... }: { marker = "u-${bobbin}-${pkgs}"; }; };
          f = framework { modules = [ { aspects.main = s1e; } ]; };
          n = builtins.head (guardsIn f.r.config.aspects.main);
        in
        {
          fired = (run { modules = [ { aspects.main = s1e; } ]; }).fired;
          absentClosed =
            (run {
              modules = [ { aspects.main = s1e; } ];
              closed = true;
              context.thimble = "x";
            }).fired;
          doorWithoutBobbin =
            (f.door {
              id = n.body.id;
              context.thimble = "x";
              sources.thimble = srcs.thimble;
            }).left.code;
        };
      expected = {
        fired = [ { nixos = "u-b-P"; } ];
        absentClosed = [ "not-fired" ];
        doorWithoutBobbin = "required-coordinate-absent";
      };
    };

    test-registration-ids-come-from-the-written-position = {
      expr = {
        reorder = (ids [ (A true) (B true) C ] "main") == (ids [ C (B true) (A true) ] "main");
        siblingMkIf = (ids [ (A true) (B true) ] "main") == (ids [ (A true) (B false) ] "main");
        # the function's door node (it reads `thimble`); the mkIf'd sibling's (`bobbin`) comes and goes
        inModuleMkIf =
          let
            fnRef =
              cond: builtins.filter (r: builtins.match ".*thimble.*" r != null) (ids [ (Am cond) ] "main").refs;
          in
          fnRef true == fnRef false && builtins.length (fnRef true) == 1;
        sameAsControl = (ids [ (A true) ] "main") == (ids [ (A false) ] "main");
        twoAspects =
          builtins.length
            (ids [
              {
                key = "mod-S";
                config.aspects.main = shared;
                config.aspects.other = shared;
              }
            ] "main").ids;
        twoModules =
          builtins.length
            (ids [
              {
                key = "mod-S1";
                config.aspects.main = shared;
              }
              {
                key = "mod-S2";
                config.aspects.main = shared;
              }
            ] "main").refs;
        # the instrument's red control: modules keyed by index move their ids under a reorder
        indexKeysMove =
          (ids [
            { aspects.main = shared; }
            { aspects.side.description = "u"; }
          ] "main") == (ids [
            { aspects.side.description = "u"; }
            { aspects.main = shared; }
          ] "main");
      };
      expected = {
        reorder = true;
        siblingMkIf = true;
        inModuleMkIf = true;
        sameAsControl = true;
        twoAspects = 2;
        twoModules = 2;
        indexKeysMove = false;
      };
    };

    test-an-aspect-included-by-reference-registers-once = {
      expr = run {
        modules = [
          { aspects.other = shared; }
          ({ config, ... }: { aspects.main.includes = [ config.aspects.other ]; })
        ];
      };
      expected = {
        registrations = 1;
        conditions = [ (w.T.term.all [ (w.T.term.has "thimble") ]) ];
        fired = [ { description = "T-x"; } ];
      };
    };

    # The loader's aspect paths name aspect COLLECTIONS: a key there is an aspect's name, never a class
    # key or the mounted table, so an aspect named as either keeps its guard (classified only at a node).
    test-an-aspect-named-as-the-mount-or-a-class-key-keeps-its-guard =
      let
        named =
          name:
          let
            f = framework {
              modules = [
                {
                  key = "m";
                  config.aspects.${name}.nixos = { bobbin, pkgs, ... }: { marker = "delivered"; };
                }
              ];
            };
            a = f.r.config.aspects.${name};
          in
          {
            registrations = builtins.length (builtins.attrNames f.r.config.lambdas);
            guards = builtins.length (guardsIn a);
            nixos = classMarker a.nixos;
          };
        guarded = {
          registrations = 1;
          guards = 1;
          nixos = "none";
        };
      in
      {
        expr = {
          main = named "main";
          mount = named "lambdas";
          classKey = named "nixos";
          mountIncludes =
            (run {
              modules = [ { aspects.lambdas.includes = [ inner ]; } ];
              name = "lambdas";
            }).fired;
        };
        expected = {
          main = guarded;
          mount = guarded;
          classKey = guarded;
          mountIncludes = [ { description = "T-x"; } ];
        };
      };

    # The door's site runs the same walk: a closure returning an aspect by reference hands onward that
    # aspect's table unentered (its records are registrations already), never re-lowered, so no
    # registered closure is applied outside its guard.
    test-a-door-output-holding-a-referenced-aspect-carries-its-table =
      let
        f = framework {
          modules = [
            {
              key = "o";
              config.aspects.other =
                { config, ... }:
                {
                  includes = [ ({ bobbin, ... }: { description = "B-${bobbin}"; }) ];
                };
            }
            (
              { config, ... }:
              {
                key = "m";
                config.aspects.main.includes = [ ({ thimble, ... }: config.aspects.other) ];
              }
            )
          ];
        };
        out = f.fire { thimble = "x"; } (builtins.head (guardsIn f.r.config.aspects.main));
      in
      {
        expr = {
          table = map builtins.attrNames (builtins.attrValues out.lambdas);
          forces = !(w.throws out.lambdas);
        };
        expected = {
          table = [
            [
              "codomain"
              "fn"
            ]
          ];
          forces = true;
        };
      };

    # One module handed to the loader twice under one loader key: two records under one id, compared by
    # the root table's `==`. An evaluator split, pre-existing at the load-time closure and enumerated:
    # an evaluator that compares a function by its lambda and environment (Lix) serves the pair, one that
    # compares the value slot (Nix, Determinate) refuses it by name (`../tests-error.nix`'s E1 message).
    test-one-module-loaded-twice-is-the-enumerated-evaluator-split =
      let
        lambdaEnvEq =
          let
            f = x: x;
          in
          f == f;
        twice =
          mod:
          let
            cnf0 = {
              entityKinds = null;
              inherit keySemantics;
              inherit (w) moduleArgs;
              aspectModules = [ (R.lambdasMount "lambdas") ];
            };
            schema = aspects.mkAspectSchema cnf0;
            load = R.defunctionalize {
              cnf = cnf0;
              key = "s1:0";
              lambdasPath = [ "lambdas" ];
              aspectPaths = [ [ "aspects" ] ];
            };
            r = merge.evalModuleTree { } [
              { options.schema = schema.schemaOption; }
              (schema.mkAspectModule { })
              {
                options.lambdas = R.lambdas;
                config._module.args.pkgs = "P";
              }
              (load mod)
              (load mod)
            ];
            vocab = aspects.mkGuardVocab (
              cnf0
              // {
                ref = R.mkApply {
                  inherit (r.config) lambdas;
                  cnf = cnf0;
                };
              }
            );
            fired = map (vocab.applyGuardWith {
              context = ctx;
              sources = srcs;
              scope = { };
            }) (guardsIn r.config.aspects.main);
          in
          {
            fired = if w.throws fired then "refused" else fired;
            # the refusal is the root table's own conflict over the one id, never another throw
            root = !(w.throws r.config.lambdas);
            ids = builtins.length (builtins.attrNames r.config.lambdas);
          };
      in
      {
        expr = {
          loadTime = twice { config.aspects.main.includes = [ inner ]; };
          inResult = twice { config.aspects.main = shared; };
        };
        expected =
          let
            arm = {
              fired =
                if lambdaEnvEq then
                  [
                    { description = "T-x"; }
                    { description = "T-x"; }
                  ]
                else
                  "refused";
              root = lambdaEnvEq;
              ids = 1;
            };
          in
          {
            loadTime = arm;
            inResult = arm;
          };
      };

    test-the-door-is-fed-inside-the-one-evaluation = {
      expr =
        let
          f = framework {
            modules = [
              { aspects.main = shared; }
              (
                { config, ... }:
                {
                  options.fired = merge.mkOption { type = merge.types.raw; };
                  config.fired = map (
                    (aspects.mkGuardVocab {
                      entityKinds = null;
                      inherit keySemantics;
                      inherit (w) moduleArgs;
                      ref = R.mkApply {
                        inherit (config) lambdas;
                        cnf = {
                          entityKinds = null;
                          inherit keySemantics;
                          inherit (w) moduleArgs;
                          aspectModules = [ (R.lambdasMount "lambdas") ];
                        };
                      };
                    }).applyGuardWith
                      {
                        context = ctx;
                        sources = srcs;
                        scope = { };
                      }
                  ) (guardsIn config.aspects.main);
                }
              )
            ];
          };
        in
        f.r.config.fired;
      expected = [ { description = "T-x"; } ];
    };
  };
}
