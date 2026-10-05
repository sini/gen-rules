# THE SECOND TEST OUTPUT — cells whose subject is an ERROR MESSAGE. THAT a construction refuses is a
# boolean and `tryEval` asserts it in the suites; WHICH refusal fired is a claim about the message,
# which `tryEval` discards. The batch asserter behind `checks.default` forces every `expr`
# UNCONDITIONALLY, so these live on `flake.testsError`, outside `./tests`:
#
#   nix-unit --flake ./ci#testsError
#
# ★★ `expectedError.msg` IS SEARCHED, NOT WHOLE-MATCHED, so every pattern is anchored at both ends
# and built by ESCAPING THE LITERAL TEXT.
#
# The door's refusals are VALUES (`{ left = { code; witness; }; }`) and are read by code in
# `./tests/door.nix`; the refusals here are the ones that throw: the loader's, at the position that
# holds the refused function, and the catalogue's, at the pattern's call.
{
  genRules,
  genAlgebra,
  genIdentity,
  genAspects,
  genProgram,
  genMerge,
  genPrelude,
  ...
}@args:
let
  w = import ./tests/_fixtures/world.nix args;
  inherit (w) R t framework;
  exactly = msg: "^" + genPrelude.escapeRegex msg + "$";
  node = modules: name: (framework { inherit modules; }).node name;
  # S1 arm (a): the framework that mounts the registration table in the aspect submodule.
  s1 = import ./tests/_fixtures/mounted.nix args;
  s1Fire =
    modules: context:
    let
      f = s1.framework { inherit modules; };
    in
    map (f.fire context) (s1.guardsIn f.r.config.aspects.main);
  firstLine = msg: "^" + genPrelude.escapeRegex msg;
in
{
  flake.testsError = {
    test-a-function-at-a-class-key-over-an-undeclared-coordinate-is-refused-by-name = {
      expr = builtins.deepSeq (node [
        { fw.aspects.bad.nixos = { undeclaredCoord, ... }: { }; }
      ] "bad") null;
      expectedError.msg = exactly "gen-rules.defunctionalize: fixture:0 at [\"fw\",\"aspects\",\"bad\",\"nixos\"]: a function at a class key that is neither a module function of `cnf.moduleArgs` nor a closure over declared coordinates; declare a module function of `cnf.moduleArgs`, or a closure at an aspect position";
    };

    test-a-function-whose-pattern-cannot-be-read-is-refused-by-name = {
      expr = builtins.deepSeq (node [ { fw.aspects.prim = builtins.head; } ] "prim") null;
      expectedError.msg = exactly "gen-rules.defunctionalize: fixture:0 at [\"fw\",\"aspects\",\"prim\"]: a function whose pattern cannot be read (a primop, or a functor whose __functor is not a lambda); write a closure with a formals pattern, an open pattern or `{ }:`";
    };

    test-a-conditional-edge-without-unless-is-refused-by-name = {
      expr = R.conditionalEdge {
        head = "e";
        when = t.always;
        relata = [ "bolt" ];
      };
      expectedError.msg = exactly "gen-rules.conditionalEdge: missing [\"unless\"] (`unless = null` is written for an edge no abnormality defeats)";
    };

    test-a-lambda-condition-is-refused-by-name = {
      expr = R.conditionalEdge {
        head = "e";
        when = _: true;
        unless = null;
        relata = [ "bolt" ];
      };
      expectedError.msg = exactly "gen-rules.conditionalEdge: `when` is a condition term (has, not, all, always); received a lambda";
    };

    test-an-unknown-pattern-field-is-refused-by-name = {
      expr = R.abnormality {
        head = "e";
        when = t.always;
        relata = [ "bolt" ];
        unless = null;
      };
      expectedError.msg = exactly "gen-rules.abnormality: unknown field(s) [\"unless\"]";
    };

    # Two registrations under one id, from different closures: the root table's own merge refuses by
    # name. The second is written straight to another aspect's mounted table (the loader carries it).
    test-a-duplicate-registration-id-is-refused-by-name =
      let
        # the id the loader gives `shared`'s closure at `main` (module key `s1:0`), written out so the
        # cell's listing never evaluates the framework
        id = builtins.toJSON {
          declared = {
            reads = [ "thimble" ];
            site = builtins.toJSON [
              "s1:0"
              [
                "aspects"
                "main"
                "includes"
                0
              ]
            ];
          };
        };
      in
      {
        expr = builtins.deepSeq (s1Fire [
          { aspects.main = s1.shared; }
          {
            aspects.z.lambdas.${id} = {
              fn = { thimble, ... }: { description = "other-${thimble}"; };
              codomain = "guard";
            };
          }
        ] s1.ctx) null;
        expectedError.msg = firstLine "gen-merge: the option `lambdas.${builtins.toJSON id}' has conflicting definitions:";
      };

    test-the-aspect-mount-needs-config-among-the-module-arguments = {
      expr = builtins.deepSeq (R.defunctionalize {
        cnf = {
          entityKinds = null;
          keySemantics.nixos.category = "class";
          moduleArgs.pkgs = true;
          aspectModules = [ (R.lambdasMount "lambdas") ];
        };
        key = "s1:0";
        lambdasPath = [ "lambdas" ];
        aspectPaths = [ [ "aspects" ] ];
      } { aspects.main = { pkgs, ... }: { }; }) null;
      expectedError.msg = exactly "gen-rules.defunctionalize: `cnf.aspectModules` mounts gen-rules' registration table, so a module function at an aspect position is handed to gen-aspects inside a `{ config, ... }:` module, and `config` is not in `cnf.moduleArgs`: gen-aspects would read that module as a context closure. Declare `config` in `cnf.moduleArgs` (the module system passes it to every module).";
    };

    # S1 arm (a) is required wherever the loader lowers aspect positions: an unmounted framework would
    # carry a module function unentered and drop a class closure's guard silently (s1c).
    test-a-loader-over-aspect-positions-without-the-mount-is-refused-by-name = {
      expr = builtins.deepSeq (R.defunctionalize {
        cnf = {
          entityKinds = null;
          keySemantics.nixos.category = "class";
          inherit (w) moduleArgs;
        };
        key = "s1:0";
        lambdasPath = [ "lambdas" ];
        aspectPaths = [ [ "aspects" ] ];
      } { aspects.main = { config, ... }: { nixos = { bobbin, ... }: { }; }; }) null;
      expectedError.msg = exactly "gen-rules.defunctionalize: `aspectPaths` is set and `cnf.aspectModules` holds no `lambdasMount`: a module function written at an aspect position would be carried unentered, and a closure in its result would reach gen-aspects unlowered (at a class key, delivered with its guard dropped). Mount gen-rules' registration table inside the aspect submodule: put `genRules.lambdasMount \"<name>\"` in `cnf.aspectModules`, and hand that one cnf to `mkAspectSchema`, `defunctionalize` and `mkApply`.";
    };

    test-a-second-mount-is-refused-by-name = {
      expr = builtins.deepSeq (R.defunctionalize {
        cnf = {
          entityKinds = null;
          keySemantics.nixos.category = "class";
          inherit (w) moduleArgs;
          aspectModules = [
            (R.lambdasMount "lambdas")
            (R.lambdasMount "closures")
          ];
        };
        key = "s1:0";
        lambdasPath = [ "lambdas" ];
        aspectPaths = [ [ "aspects" ] ];
      } { }) null;
      expectedError.msg = exactly "gen-rules.defunctionalize: `cnf.aspectModules` holds 2 `lambdasMount` entries (lambdas, closures): a framework mounts gen-rules' registration table once.";
    };

    # Inside the aspect submodule the mount's name is the registration table, so a nested aspect of that
    # name is table content: the table holds registration records only and refuses anything else.
    test-a-nested-aspect-named-as-the-mount-is-refused-by-name = {
      expr =
        builtins.attrNames
          (s1.framework {
            modules = [ { aspects.main.lambdas.nixos = { bobbin, pkgs, ... }: { marker = "delivered"; }; } ];
          }).r.config.lambdas;
      expectedError.msg = exactly "gen-rules.lambdasMount: `lambdas` is gen-rules' registration table, mounted inside the aspect submodule, and it holds [\"nixos\"], which are not registration records (`{ fn; codomain; }`): a nested aspect cannot be named `lambdas`. Rename the aspect, or mount the table under another name.";
    };

    # The one mismatch the mount leaves formable: the schema built from a cnf WITHOUT the mount while the
    # loader and the door read one WITH it. The table key is then a freeform nested aspect, and the
    # registered closure is refused by gen-aspects at its position, never served.
    test-a-schema-without-the-mount-refuses-the-registered-closure-at-its-position =
      let
        cnf0 = {
          entityKinds = null;
          keySemantics.nixos.category = "class";
          inherit (w) moduleArgs;
          aspectModules = [ (R.lambdasMount "lambdas") ];
        };
        schema = w.aspects.mkAspectSchema (builtins.removeAttrs cnf0 [ "aspectModules" ]);
        r = w.merge.evalModuleTree { } [
          { options.schema = schema.schemaOption; }
          (schema.mkAspectModule { })
          {
            options.lambdas = R.lambdas;
            config._module.args.pkgs = "P";
          }
          (R.defunctionalize {
            cnf = cnf0;
            key = "s1:0";
            lambdasPath = [ "lambdas" ];
            aspectPaths = [ [ "aspects" ] ];
          } { config.aspects.main = s1.shared; })
        ];
        vocab = w.aspects.mkGuardVocab (
          cnf0
          // {
            ref = R.mkApply {
              inherit (r.config) lambdas;
              cnf = cnf0;
            };
          }
        );
      in
      {
        expr = builtins.deepSeq (map (vocab.applyGuardWith {
          context = s1.ctx;
          sources = s1.srcs;
          scope = { };
        }) (s1.guardsIn r.config.aspects.main)) null;
        expectedError.msg = firstLine "gen-aspects: aspect `main.lambdas.{\"declared\":{\"reads\":[\"thimble\"],\"site\":\"[\\\"s1:0\\\",[\\\"aspects\\\",\\\"main\\\",\\\"includes\\\",0]]\"}}.fn`: a context closure reached a gen-aspects-typed position.";
      };

    # s1e: a class closure inside a module function, reading `bobbin`, fired at a context without it
    # under the open world: refused at the door node by name, never in gen-merge.
    test-s1e-at-a-context-without-its-coordinate-is-refused-by-name = {
      expr = builtins.deepSeq (s1Fire [
        { aspects.main = { config, ... }: { nixos = { bobbin, pkgs, ... }: { marker = "u-${bobbin}"; }; }; }
      ] { thimble = "x"; }) null;
      expectedError.msg = exactly "gen-aspects.guard: aspect `main.includes.[definition 1-entry 1]`: absent-coordinate: {\"name\":\"bobbin\"}";
    };
  };
}
