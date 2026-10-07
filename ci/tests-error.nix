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
  # A closure's output fired at a context without `bobbin`, then applied downstream as an aspect
  # definition (den-hoag-zm0gu).
  s1Down =
    out:
    let
      f = s1.framework { modules = [ { config.aspects.main.includes = [ out ]; } ]; };
      o = f.fire { thimble = "x"; } (builtins.head (s1.guardsIn f.r.config.aspects.main));
      cnf0 = {
        entityKinds = null;
        keySemantics.nixos.category = "class";
        inherit (s1.w) moduleArgs;
        aspectModules = [ (R.lambdasMount "lambdas") ];
      };
      schema = s1.w.aspects.mkAspectSchema cnf0;
      p =
        (s1.w.merge.evalModuleTree { } [
          { options.schema = schema.schemaOption; }
          (schema.mkAspectModule { })
          { config.aspects.probe = o; }
        ]).config.aspects.probe;
    in
    builtins.deepSeq (builtins.attrNames p) (
      map (x: x.nixos or null) (p.includes or [ ]) ++ [ p.nixos ] ++ s1.guardsIn p
    );
  zmId = "{\"declared\":{\"reads\":[\"thimble\"],\"site\":\"[\\\"s1:0\\\",[\\\"aspects\\\",\\\"main\\\",\\\"includes\\\",0]]\"}}";
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

    # Two registrations under one id, from different closures, both on the closure's own position: the
    # door unites the tables it reaches and refuses by name. The second is written straight to the
    # aspect's mounted table (the loader carries it).
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
            # spelled as the loader's own record, so the table admits it and the door meets both
            aspects.main.lambdas.${id} = {
              inherit id;
              fn = { thimble, ... }: { description = "other-${thimble}"; };
              codomain = "guard";
            };
          }
        ] s1.ctx) null;
        expectedError.msg = genPrelude.escapeRegex ": duplicate-registration: 2 tables on the closure's own position register ";
      };

    # A record written by hand into an aspect's table, off the closure's position, where the door never
    # looks: the table refuses it by name when it is read (ADR-0025 item 1), never drops it.
    test-a-record-the-loader-did-not-make-is-refused-by-name = {
      expr =
        s1.registered
          (s1.framework {
            modules = [
              { aspects.main = s1.shared; }
              {
                aspects.z.lambdas.${zmId} = {
                  fn = { thimble, ... }: { description = "forged-${thimble}"; };
                  codomain = "guard";
                };
              }
            ];
          }).r.config.lambdas;
      expectedError.msg = genPrelude.escapeRegex "gen-rules.lambdasMount: `lambdas` holds records under [";
    };

    # The same record naming its own key: the mark is a well-formedness check, not provenance (anyone
    # can write it, den-hoag-uw098), so the mount admits it, and the enumerator, uniting the records
    # under one id by the door's `==`, refuses the differing pair by name.
    test-a-differing-record-naming-its-key-is-refused-by-the-enumerator = {
      expr =
        s1.registered
          (s1.framework {
            modules = [
              { aspects.main = s1.shared; }
              {
                aspects.z.lambdas.${zmId} = {
                  id = zmId;
                  fn = { thimble, ... }: { description = "forged-${thimble}"; };
                  codomain = "guard";
                };
              }
            ];
          }).r.config.lambdas;
      expectedError.msg = exactly "gen-rules.registrations: duplicate-registration: [${builtins.toJSON zmId}] are registered by records that differ";
    };

    # A load-time closure is registered at the root, and its firing still reads the tables on its own
    # position: a record written there by hand is refused by the mount, and one naming its key unites
    # with the root's and is refused by the door, never passed over because the root holds the id.
    test-a-hand-written-record-on-a-load-time-closures-position-is-refused-by-name = {
      expr = builtins.deepSeq (s1Fire [
        { aspects.main.includes = [ s1.inner ]; }
        {
          aspects.main.lambdas.${zmId} = {
            fn = { thimble, ... }: { description = "forged-${thimble}"; };
            codomain = "guard";
          };
        }
      ] s1.ctx) null;
      expectedError.msg = genPrelude.escapeRegex "gen-rules.lambdasMount: `lambdas` holds records under [";
    };

    test-a-differing-record-naming-its-key-on-a-load-time-closures-position-is-refused-by-name = {
      expr = builtins.deepSeq (s1Fire [
        { aspects.main.includes = [ s1.inner ]; }
        {
          aspects.main.lambdas.${zmId} = {
            id = zmId;
            fn = { thimble, ... }: { description = "forged-${thimble}"; };
            codomain = "guard";
          };
        }
      ] s1.ctx) null;
      expectedError.msg = genPrelude.escapeRegex ": duplicate-registration: 2 tables on the closure's own position register ";
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
        s1.registered
          (s1.framework {
            modules = [ { aspects.main.lambdas.nixos = { bobbin, pkgs, ... }: { marker = "delivered"; }; } ];
          }).r.config.lambdas;
      expectedError.msg = exactly "gen-rules.lambdasMount: `lambdas` is gen-rules' registration table, mounted inside the aspect submodule, and it holds [\"nixos\"], which are not registration records (`{ fn; codomain; }`): a nested aspect cannot be named `lambdas`. Rename the aspect, or mount the table under another name.";
    };

    # The one mismatch the mount leaves formable: the schema built from a cnf WITHOUT the mount while the
    # loader and the door read one WITH it. The table key is then a freeform nested aspect, and the
    # registered record is refused by gen-aspects at its position, never served.
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
        # the record's two leaves under gen-aspects' freeform slot are both refused, and which one
        # is named first is the evaluator's order: its identifier (a string; Nix, Determinate) or its
        # closure (Lix)
        expectedError.msg =
          genPrelude.escapeRegex "gen-aspects: aspect `main"
          + "(`: orphan leaf at `main\\.lambdas\\..*\\.id` \\(a value of type string|\\.lambdas\\..*\\.fn`: a context closure reached a gen-aspects-typed position)";
      };

    # s1e: a class closure inside a module function, reading `bobbin`, fired at a context without it
    # under the open world: refused at the door node by name, never in gen-merge.
    test-s1e-at-a-context-without-its-coordinate-is-refused-by-name = {
      expr = builtins.deepSeq (s1Fire [
        { aspects.main = { config, ... }: { nixos = { bobbin, pkgs, ... }: { marker = "u-${bobbin}"; }; }; }
      ] { thimble = "x"; }) null;
      expectedError.msg = exactly "gen-aspects.guard: aspect `main.includes.[definition 1-entry 1]`: absent-coordinate: {\"name\":\"bobbin\"}";
    };

    # den-hoag-zm0gu: a closure in the result of a module function a closure returned.
    test-a-closure-in-a-module-function-output-is-refused-by-name = {
      expr = builtins.deepSeq (s1Down (
        { thimble, ... }: { config, ... }: { nixos = { bobbin, pkgs, ... }: { }; }
      )) null;
      expectedError.msg = exactly "gen-rules.mkApply: guard-codomain: the closure registered under ${zmId} returned a module function whose result holds a closure at [\"nixos\"]; the door cannot register it, because it exists only under the module system's arguments. Write the closure in an attrset output, where it becomes a nested door node, or as a guard term.";
    };

    # den-hoag-zm0gu: the includes form, which gen-aspects refused with a hint naming the framework's
    # surface the closure was already written through.
    test-an-include-closure-in-a-module-function-output-is-refused-by-name = {
      expr = builtins.deepSeq (s1Down (
        { thimble, ... }: { config, ... }: { includes = [ ({ bobbin, ... }: { }) ]; }
      )) null;
      expectedError.msg = exactly "gen-rules.mkApply: guard-codomain: the closure registered under ${zmId} returned a module function whose result holds a closure at [\"includes\",0]; the door cannot register it, because it exists only under the module system's arguments. Write the closure in an attrset output, where it becomes a nested door node, or as a guard term.";
    };

    # den-hoag-zm0gu: the same refusal for a module function at an aspect position of an attrset output,
    # named at the closure's own position.
    test-a-closure-in-a-nested-module-function-output-is-refused-by-name = {
      expr = builtins.deepSeq (s1Down (
        { thimble, ... }:
        {
          includes = [ ({ config, ... }: { nixos = { bobbin, pkgs, ... }: { }; }) ];
        }
      )) null;
      expectedError.msg = exactly "gen-rules.mkApply: guard-codomain: the closure registered under ${zmId} returned a module function whose result holds a closure at [\"includes\",0,\"nixos\"]; the door cannot register it, because it exists only under the module system's arguments. Write the closure in an attrset output, where it becomes a nested door node, or as a guard term.";
    };

    # den-hoag-zm0gu: a functor-form module function returned by a closure meets the attrset output's
    # check, never a silent drop.
    test-a-functor-module-function-output-is-refused-by-name = {
      expr = builtins.deepSeq (s1Down (
        { thimble, ... }:
        {
          __functionArgs.config = false;
          __functor = _: { config, ... }: { nixos = { pkgs, ... }: { }; };
        }
      )) null;
      expectedError.msg = exactly "gen-aspects.guard: aspect `main.includes.[definition 1-entry 1]`: guard-codomain: the closure's output holds a `__functor` record at an aspect position (design open item 9: the framework's vocabulary) at []";
    };

    # iy9qh R3: a top-level functor whose `__functor` yields no lambda is left unwrapped, and the module
    # system refuses it for that attribute. The message is gen-merge's, so the cell pins the attribute it
    # names, not its wording; `module-fn-shapes` holds the value-plane cell that it refuses catchably.
    test-a-malformed-functor-top-level-module-is-refused-at-its-functor = {
      expr =
        builtins.deepSeq
          (s1.framework {
            modules = [ { __functor = _: 5; } ];
          }).r.config.aspects.main.description
          null;
      expectedError.msg = ".*__functor.*";
    };

    # den-hoag-crk5e: the lift moves a class-key closure into `includes`; an override or order property
    # would rank it there against other definitions, so it is refused by name, the wrapper's `_type` named.
  }
  # den-hoag-iy9qh R4: a functor whose pattern cannot be read (its `__functor` yields no lambda, or its
  # `__functionArgs` is not a map to Booleans) is refused by name at a class key, at the loader (its
  # class value and its includes forced, trap 371befb3) and in a door's output, never an uncatchable abort.
  // builtins.listToAttrs (
    builtins.concatMap
      (c: [
        {
          name = "test-a-malformed-functor-${c.name}-at-a-class-key-is-refused-by-name";
          value = {
            expr =
              let
                main = (s1.framework { modules = [ { aspects.main.nixos = c.value; } ]; }).r.config.aspects.main;
              in
              builtins.deepSeq [ main.nixos (s1.guardsIn main) ] null;
            expectedError.msg = exactly "gen-rules.defunctionalize: s1:0 at [\"aspects\",\"main\",\"nixos\"]: a function at a class key that is neither a module function of `cnf.moduleArgs` nor a closure over declared coordinates; declare a module function of `cnf.moduleArgs`, or a closure at an aspect position";
          };
        }
        {
          name = "test-a-malformed-functor-${c.name}-at-a-class-key-in-a-door-output-is-refused-by-name";
          value = {
            expr = builtins.deepSeq (s1Fire [
              { aspects.main.includes = [ ({ thimble, ... }: { nixos = c.value; }) ]; }
            ] s1.ctx) null;
            expectedError.msg = exactly "gen-aspects.guard: aspect `main.includes.[definition 1-entry 1]`: guard-codomain: the closure's output holds a function at a class key that is neither a module function of `cnf.moduleArgs` nor a closure over declared coordinates at [\"nixos\"]";
          };
        }
      ])
      [
        {
          name = "returning-an-integer";
          value.__functor = _: 5;
        }
        {
          name = "whose-functor-is-not-a-function";
          value.__functor = 5;
        }
        {
          name = "with-integer-functionargs";
          value = {
            __functionArgs = 5;
            __functor = _: { bobbin, ... }: { };
          };
        }
        {
          name = "with-non-boolean-functionargs";
          value = {
            __functionArgs.bobbin = 5;
            __functor = _: { bobbin, ... }: { };
          };
        }
        {
          # Nix applies it, but nixpkgs' one-level `lib.isFunction` does not call it a function
          name = "yielding-a-functor";
          value.__functor = _: { __functor = _: { bobbin, ... }: { }; };
        }
      ]
  )
  // builtins.listToAttrs (
    map
      (c: {
        name = "test-a-class-key-closure-under-${c.ctor}-is-refused-by-name";
        value = {
          expr =
            builtins.deepSeq
              (s1.framework {
                modules = [ { aspects.main.nixos = c.wrap ({ bobbin, pkgs, ... }: { }); } ];
              }).r.config.aspects.main.nixos
              null;
          expectedError.msg = exactly "gen-rules.defunctionalize: s1:0 at [\"aspects\",\"main\",\"nixos\"]: a closure over coordinates at a class key under a property wrapper of `_type = \"${c.type}\"` (`mkOverride`/`mkForce`/`mkDefault`, or `mkOrder`/`mkBefore`/`mkAfter`): the lift moves the definition into `includes`, where that property would rank it against other definitions than the ones it was written beside; write the closure at an aspect position (`includes`), with the property on the definition it ranks there";
        };
      })
      [
        {
          ctor = "mkForce";
          type = "override";
          wrap = w.merge.mkForce;
        }
        {
          ctor = "mkBefore";
          type = "order";
          wrap = w.merge.mkBefore;
        }
      ]
  )
  # den-hoag-p5k3k (crk5e P-3): the same closure in a door's output is refused by the guard codomain, at
  # its position in the output.
  // builtins.listToAttrs (
    map
      (c: {
        name = "test-a-class-key-closure-under-${c.ctor}-in-a-door-output-is-refused-by-name";
        value = {
          expr =
            let
              f = s1.framework {
                modules = [
                  {
                    aspects.main.includes = [ ({ thimble, ... }: { nixos = c.wrap ({ bobbin, pkgs, ... }: { }); }) ];
                  }
                ];
              };
            in
            builtins.deepSeq (f.fire s1.ctx (builtins.head (s1.guardsIn f.r.config.aspects.main))) null;
          expectedError.msg = exactly "gen-aspects.guard: aspect `main.includes.[definition 1-entry 1]`: guard-codomain: the closure's output holds a closure over coordinates at a class key under a property wrapper of `_type = \"${c.type}\"` (`mkOverride`/`mkForce`/`mkDefault`, or `mkOrder`/`mkBefore`/`mkAfter`): the lift moves the definition into `includes`, where that property would rank it against other definitions than the ones it was written beside at [\"nixos\"]";
        };
      })
      [
        {
          ctor = "mkForce";
          type = "override";
          wrap = w.merge.mkForce;
        }
        {
          ctor = "mkBefore";
          type = "order";
          wrap = w.merge.mkBefore;
        }
      ]
  );
}
