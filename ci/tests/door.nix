# THE DOOR (`mkApply`): the only place in gen a closure is applied. Every refusal is a value
# `{ left = { code; witness; }; }`, so these cells read the arm the door took by its code; the
# messages are the error plane's.
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
  w = import ./_fixtures/world.nix args;
  inherit (w)
    R
    T
    D
    framework
    tuck
    ctx
    srcs
    src
    code
    throws
    fire1
    program
    ;
  fx = modules: framework { inherit modules; };

  shapes = fx [
    {
      fw.aspects = {
        formals = tuck;
        open =
          { ... }@a:
          {
            description = builtins.concatStringsSep "," (builtins.attrNames a);
          };
        narrow =
          { thimble, ... }@a:
          {
            description = builtins.concatStringsSep "," (builtins.attrNames a);
          };
      };
    }
  ];
  outer = fx [
    {
      fw.aspects.outer =
        { thimble, ... }:
        {
          description = "outer-${thimble}";
          includes = [ ({ spool, ... }: { description = "inner-${thimble}-${spool}"; }) ];
        };
    }
  ];
  outerId = (outer.node "outer").body.id;
  outerOut =
    (outer.door {
      id = outerId;
      context = ctx;
      sources = srcs;
    }).right;
  nestedId = builtins.head (builtins.attrNames outerOut.scope);

  ruleWith =
    contract: body:
    framework {
      ruleContract = contract;
      modules = [ { fw.rules.p = body; } ];
    };
  member = payload: {
    ctor = "member";
    kind = "tuck";
    inherit payload;
  };
  fireRule =
    f:
    f.door {
      id = f.config.rules.p.body.id;
      context = ctx;
      sources = srcs;
    };
  rule = ruleWith {
    emits = [ "tuck" ];
    binds = null;
    suppresses = [ ];
  } ({ thimble, ... }: [ (member { anything = thimble; }) ]);
  ruleBody =
    clauses:
    program.body {
      name = "cell";
      declared = D;
      inherit clauses;
    };

  # A door applied to an id built by hand: the identify step must be total over its argument.
  doorOn =
    id:
    code (
      shapes.door {
        inherit id;
        context = ctx;
        sources = srcs;
      }
    );
in
{
  flake.tests.door = {
    # A formals pattern receives exactly its formals.
    test-door-formals-narrowed = {
      expr = {
        tuck = fire1 shapes "formals";
        received = fire1 shapes "narrow";
      };
      expected = {
        tuck.description = "tuck-x";
        received.description = "thimble";
      };
    };

    # An open pattern receives the context restricted to D (`extra` is not declared).
    test-door-open-restricted-to-D = {
      expr = fire1 shapes "open";
      expected.description = "bobbin,spool,thimble";
    };

    # `{ ... }@args` read past its formals.
    test-door-past-formals = {
      expr = fire1 (fx [
        {
          fw.aspects.past =
            { ... }@a:
            {
              description = if a ? spool then "spool:${a.spool}" else "none";
            };
        }
      ]) "past";
      expected.description = "spool:s";
    };

    # Under E = [ thimble ], an open pattern is narrowed to the entity kinds.
    test-door-entity-kinds = {
      expr =
        let
          f = fx [
            {
              fw.aspects.k =
                { ... }@a:
                {
                  description = builtins.concatStringsSep "," (builtins.attrNames a);
                };
            }
          ];
          door = R.mkApply {
            lambdas = f.config.lambdas;
            inherit (f) cnf;
            declared = D;
            entityKinds = [ "thimble" ];
          };
        in
        (door {
          id = (f.node "k").body.id;
          context = ctx;
          sources = srcs;
        }).right.output;
      expected.description = "thimble";
    };

    # A function at `description` is outside the guard codomain.
    test-door-guard-codomain = {
      expr =
        let
          f = fx [ { fw.aspects.leak = { thimble }: { description = x: x; }; } ];
        in
        code (
          f.door {
            id = (f.node "leak").body.id;
            context = ctx;
            sources = srcs;
          }
        );
      expected = "guard-codomain";
    };

    # A module function of `cnf.moduleArgs` at a class key in the output is a module slot, admitted.
    test-door-module-slot-admitted = {
      expr = builtins.attrNames (
        builtins.functionArgs
          (fire1 (fx [
            { fw.aspects.slot = { thimble }: { nixos = { pkgs, ... }: { marker = thimble; }; }; }
          ]) "slot").nixos
      );
      expected = [ "pkgs" ];
    };

    # The door rule admitted by gen-program's `body` and fired by `groundInstances` through the door.
    test-door-rule-fires = {
      expr = map (d: builtins.removeAttrs d [ "__mint" ]) (
        program.groundInstances {
          sources = srcs;
          door = rule.door;
        } ctx (ruleBody [ rule.config.rules.p ])
      );
      expected = [
        {
          ctor = "member";
          kind = "tuck";
          payload.anything = "x";
        }
      ];
    };

    # A `binds` breach and a `suppresses` breach in one output, both named.
    test-door-rule-breach = {
      expr =
        let
          r = fireRule (
            ruleWith
              {
                emits = [ "tuck" ];
                binds = [ "only" ];
                suppresses = [ ];
              }
              (
                { thimble, ... }:
                [
                  (member { other = thimble; })
                  {
                    ctor = "suppress";
                    target = "z";
                  }
                ]
              )
          );
        in
        {
          c = code r;
          b = r.left.witness.breaches or null;
        };
      expected = {
        c = "codomain-breach";
        b = [
          {
            field = "binds";
            names = [ "other" ];
          }
          {
            field = "suppresses";
            names = [ "z" ];
          }
        ];
      };
    };

    # A `null` `binds`/`suppresses` is the over-approximation, and a door rule declaring it FIRES: the
    # door returns `right` for its binding and suppressing declarations, never a refusal and never an
    # abort. gen-program's own check reads `null` as admit-all; at a gen-program whose check does not,
    # this cell aborts.
    test-door-rule-null-admits = {
      expr =
        let
          out = [
            (member { anything = "a"; })
            {
              ctor = "suppress";
              target = "z";
            }
          ];
          open = fireRule (
            ruleWith {
              emits = [
                "tuck"
                "suppress"
              ];
              binds = null;
              suppresses = null;
            } (_: out)
          );
          # The same output against finite sets that exclude its names: refused, so the
          # admission above is the `null`'s doing.
          closed = fireRule (
            ruleWith {
              emits = [
                "tuck"
                "suppress"
              ];
              binds = [ ];
              suppresses = [ ];
            } (_: out)
          );
        in
        {
          open = code open;
          closed = code closed;
        };
      expected = {
        open = "right";
        closed = "codomain-breach";
      };
    };

    # A rule closure's output must be a list of declarations gen-program's rows know.
    test-door-rule-codomain = {
      expr = {
        notAList = code (
          fireRule (
            ruleWith
              {
                emits = [ "tuck" ];
                binds = null;
                suppresses = [ ];
              }
              (_: {
                ctor = "member";
              })
          )
        );
        noCtor = code (
          fireRule (
            ruleWith {
              emits = [ "tuck" ];
              binds = null;
              suppresses = [ ];
            } (_: [ { kind = "tuck"; } ])
          )
        );
      };
      expected = {
        notAList = "rule-codomain";
        noCtor = "rule-codomain";
      };
    };

    # The inner closure resolved through the scope the outer's firing returned.
    test-door-nested-scope = {
      expr = fire1 outer "outer";
      expected = {
        description = "outer-x";
        includes = [ { description = "inner-x-s"; } ];
      };
    };

    # The nested id resolved with no `captured`: the door re-applies the outer (the fallback).
    test-door-nested-fallback = {
      expr =
        (outer.door {
          id = nestedId;
          context = ctx;
          sources = srcs;
        }).right.output;
      expected.description = "inner-x-s";
    };

    test-door-source-rebound = {
      expr = code (
        outer.door {
          id = nestedId;
          context = ctx;
          sources = srcs // {
            thimble = src "elsewhere";
          };
        }
      );
      expected = "source-rebound";
    };

    # Nested ids are equal across coordinate values from one source, and differ across sources.
    test-door-output-identity-by-source = {
      expr =
        let
          k =
            s: c:
            builtins.attrNames
              (outer.door {
                id = outerId;
                context = c;
                sources = s;
              }).right.scope;
        in
        {
          valuesDiffer = k srcs ctx == k srcs (ctx // { thimble = "y"; });
          sourcesDiffer = k srcs ctx != k (srcs // { thimble = src "u"; }) ctx;
        };
      expected = {
        valuesDiffer = true;
        sourcesDiffer = true;
      };
    };

    test-door-unregistered = {
      expr = doorOn (
        (T.refId {
          declared = {
            site = "nowhere";
            reads = [ ];
          };
        }).right
      );
      expected = "unregistered";
    };

    # THE IDENTIFY STEP IS TOTAL: anything that is not refId's whole encoding is `not-a-registration`,
    # never an abort. The truncated and ill-shaped arms abort a prefix-match-then-decode door
    # uncatchably; the live and unregistered arms are the controls.
    test-door-not-a-registration = {
      expr = {
        live = doorOn (shapes.node "formals").body.id;
        unregistered = doorOn (
          builtins.toJSON {
            declared = {
              reads = [ ];
              site = "nowhere";
            };
          }
        );
        plain = doorOn "plainstring";
        truncated = doorOn "{\"declared\":";
        declaredInt = doorOn "{\"declared\":1}";
        nestedInt = doorOn "{\"nested\":1}";
        nestedNoOuter = doorOn "{\"nested\":{\"sources\":{}}}";
        nestedBadOuter = doorOn (
          builtins.toJSON {
            nested = {
              outer = "{\"declared\":";
              position = [ ];
              reads = [ ];
              sources = { };
            };
          }
        );
        notAString = doorOn 7;
        overLong = doorOn (
          "{\"declared\":{\"reads\":[],\"site\":\""
          + builtins.concatStringsSep "" (builtins.genList (_: "a") 9000)
          + "\"}}"
        );
      };
      expected = {
        live = "right";
        unregistered = "unregistered";
        plain = "not-a-registration";
        truncated = "not-a-registration";
        declaredInt = "not-a-registration";
        nestedInt = "not-a-registration";
        nestedNoOuter = "not-a-registration";
        nestedBadOuter = "not-a-registration";
        notAString = "not-a-registration";
        overLong = "not-a-registration";
      };
    };

    # The door applied at a context lacking a required formal. Unreachable through a door node,
    # whose `has` condition is FALSE first; reached here by calling the door directly.
    test-door-required-coordinate-absent = {
      expr = {
        absent = code (
          shapes.door {
            id = (shapes.node "formals").body.id;
            context = builtins.removeAttrs ctx [ "thimble" ];
            sources = srcs;
          }
        );
        control = code (
          shapes.door {
            id = (shapes.node "formals").body.id;
            context = ctx;
            sources = srcs;
          }
        );
      };
      expected = {
        absent = "required-coordinate-absent";
        control = "right";
      };
    };

    # Under D with `thimble` absent the node's condition is FALSE: not fired.
    test-door-not-fired-when-absent = {
      expr = shapes.fire (builtins.removeAttrs ctx [ "thimble" ]) srcs (shapes.node "formals");
      expected = null;
    };

    # Under the open world an absent coordinate is refused (gen-aspects' refusal), and the same node
    # fires where the coordinate is present.
    test-door-open-world-absent-refuses = {
      expr =
        let
          f = framework {
            d = null;
            modules = [ { fw.aspects.ow = tuck; } ];
          };
        in
        {
          absent = throws (f.fire { bobbin = "b"; } srcs (f.node "ow"));
          present = f.fire { thimble = "x"; } srcs (f.node "ow");
        };
      expected = {
        absent = true;
        present.description = "tuck-x";
      };
    };
  };
}
