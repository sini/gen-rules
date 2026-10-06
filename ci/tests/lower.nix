# THE LOWERING AT THE LOADER (`defunctionalize`). A closure written at an aspect or rule position
# becomes a door node or door rule whose body is `ref r`, and the closure is registered under `r`.
# Nothing is applied: every cell here reads the lowered value or the table's keys, never a firing,
# except where it says so.
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
    framework
    form
    tuck
    ctx
    srcs
    throws
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
        empty = { }: { description = "empty"; };
        narrow =
          { thimble, ... }@a:
          {
            description = builtins.concatStringsSep "," (builtins.attrNames a);
          };
        bomb = { thimble }: throw "applied at lowering";
      };
    }
  ];
  nest = fx [
    {
      fw.aspects.deep = {
        includes = [ ({ spool, ... }: { description = "inc-${spool}"; }) ];
        child = { bobbin, ... }: { description = "child-${bobbin}"; };
        nixos = { pkgs, ... }: { marker = pkgs; };
      };
    }
  ];
  lifted = fx [
    {
      fw.aspects.lifted.nixos =
        { thimble, pkgs, ... }:
        {
          got = "${thimble}+${pkgs}";
        };
    }
  ];
  imports = fx [
    {
      imports = [
        ./_fixtures/imported.nix
        { fw.aspects.inline = tuck; }
      ];
    }
  ];
  modFn = fx [
    (
      { pkgs, ... }:
      {
        fw.aspects.byfn = { thimble, ... }: { description = "fn-${thimble}-${pkgs}"; };
      }
    )
  ];
  rule = fx [
    {
      fw.rules.p =
        { thimble, ... }:
        [
          {
            ctor = "member";
            kind = "tuck";
            payload.anything = thimble;
          }
        ];
    }
  ];
  ruleClause = rule.config.rules.p;
in
{
  flake.tests.lower = {
    # `{ thimble, bobbin ? … }`: the condition covers the REQUIRED formal, the reads carry all of them.
    test-lower-formals-node = {
      expr = form (shapes.node "formals");
      expected = {
        formerOf = "All";
        covers = [ "thimble" ];
        body = "Ref";
        reads = [
          "bobbin"
          "thimble"
        ];
      };
    };

    test-lower-open-node = {
      expr = form (shapes.node "open");
      expected = {
        formerOf = "Always";
        covers = [ ];
        body = "Ref";
        reads = null;
      };
    };

    test-lower-empty-node = {
      expr = form (shapes.node "empty");
      expected = {
        formerOf = "Always";
        covers = [ ];
        body = "Ref";
        reads = [ ];
      };
    };

    # A closure whose body throws is lowered and its node forced: the lowering applies nothing.
    test-lower-applies-nothing = {
      expr = {
        registered = builtins.length (builtins.attrNames shapes.config.lambdas);
        bomb = form (shapes.node "bomb");
      };
      expected = {
        registered = 5;
        bomb = {
          formerOf = "All";
          covers = [ "thimble" ];
          body = "Ref";
          reads = [ "thimble" ];
        };
      };
    };

    # One closure text at two positions: two identifiers, two registrations. Reds when the site drops
    # the position.
    test-lower-twin-sites-distinct = {
      expr =
        let
          f = fx [
            {
              fw.aspects.a = tuck;
              fw.aspects.b = tuck;
            }
          ];
        in
        {
          distinct = (f.node "a").body.id != (f.node "b").body.id;
          registered = builtins.length (builtins.attrNames f.config.lambdas);
        };
      expected = {
        distinct = true;
        registered = 2;
      };
    };

    test-lower-positions = {
      expr = {
        include = (builtins.head (nest.node "deep").includes).__guard or false;
        child = (nest.node "deep").child.__guard or false;
        slotKept = builtins.isFunction (nest.node "deep").nixos;
      };
      expected = {
        include = true;
        child = true;
        slotKept = true;
      };
    };

    # G3: a closure over declared coordinates at a class key is lifted to a door node in `includes`,
    # and the class key's value becomes `{ }`. Firing it yields a module of `pkgs`.
    test-lower-class-lift = {
      expr =
        let
          n = builtins.head (lifted.node "lifted").includes;
        in
        {
          classEmptied = (lifted.node "lifted").nixos;
          cond = form n;
          # read as the class's module system reads it, never by calling the class value
          applied.got =
            (w.merge.evalModuleTree { } [
              { options.got = w.merge.mkOption { type = w.merge.types.str; }; }
              { config._module.args.pkgs = "P"; }
              (lifted.fire ctx srcs n).nixos
            ]).config.got;
        };
      expected = {
        classEmptied = { };
        cond = {
          formerOf = "All";
          covers = [ "thimble" ];
          body = "Ref";
          reads = [ "thimble" ];
        };
        applied.got = "x+P";
      };
    };

    test-lower-class-refused = {
      expr = throws ((fx [ { fw.aspects.bad.nixos = { undeclaredCoord, ... }: { }; } ]).node "bad");
      expected = true;
    };

    # The aspect's attribute set never depends on a class value.
    test-lower-lazy-class-values = {
      expr =
        let
          a =
            (fx [
              {
                fw.aspects.s = {
                  nixos = throw "forced";
                  description = "d";
                };
              }
            ]).node
              "s";
        in
        {
          names = builtins.attrNames a;
          inherit (a) description;
        };
      expected = {
        names = [
          "description"
          "includes"
          "nixos"
        ];
        description = "d";
      };
    };

    # den v1's `__functor` aspect form is the framework's vocabulary: carried unlowered.
    test-lower-functor-unlowered = {
      expr =
        let
          a =
            (fx [ { fw.aspects.fn.__functor = _: { thimble, ... }: { description = thimble; }; } ]).node
              "fn";
        in
        {
          guard = a.__guard or false;
          functor = a ? __functor;
        };
      expected = {
        guard = false;
        functor = true;
      };
    };

    test-lower-mkif-content = {
      expr = ((fx [ { fw.aspects.cond = w.merge.mkIf true tuck; } ]).node "cond").__guard or false;
      expected = true;
    };

    test-lower-imports = {
      expr = {
        path = (imports.node "imported").__guard or false;
        inline = (imports.node "inline").__guard or false;
        pathSite =
          builtins.match ".*imported[.]nix.*" (builtins.fromJSON (imports.node "imported").body.id)
          .declared.site != null;
      };
      expected = {
        path = true;
        inline = true;
        pathSite = true;
      };
    };

    # A top-level module function is wrapped by its formals and applied by gen-merge, never here.
    test-lower-module-fn-wrapped = {
      expr = {
        node = (modFn.node "byfn").__guard or false;
        out = w.fire1 modFn "byfn";
      };
      expected = {
        node = true;
        out.description = "fn-x-PKGS";
      };
    };

    # A rule closure becomes gen-program's door clause, carrying the declared contract.
    test-lower-rule-door-clause = {
      expr = {
        body = ruleClause.body.__bodyTerm;
        contract = { inherit (ruleClause) emits binds suppresses; };
        admitted =
          !((w.program.body {
            name = "cell";
            declared = w.D;
            clauses = [ ruleClause ];
          }).refused or true
          );
      };
      expected = {
        body = "Ref";
        contract = {
          emits = [ "tuck" ];
          binds = null;
          suppresses = [ ];
        };
        admitted = true;
      };
    };

    # A function whose pattern cannot be read (a primop) is refused by name at its position.
    test-lower-unreadable-pattern-refused = {
      expr = {
        refused = throws ((fx [ { fw.aspects.prim = builtins.head; } ]).node "prim");
        # Control, same fixture shape: a readable closure at the same position lowers.
        control = ((fx [ { fw.aspects.prim = tuck; } ]).node "prim").__guard or false;
      };
      expected = {
        refused = true;
        control = true;
      };
    };
  };
}
