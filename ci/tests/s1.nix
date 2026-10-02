# ★ S1 — AN OPEN OWNER READING, PINNED AT TODAY'S BEHAVIOUR. These cells do not assert what is right.
#
# A closure inside the result of a module function written at an aspect position
# (`main = { config, ... }: { … }`) has no registration channel: the lowering wraps the module
# function and does not enter it, so its closures are never registered. What happens to them is
# gen-aspects', and it differs by position. These cells read the loader over gen-aspects' REAL aspect
# schema (not the fixture's raw option) and pin the measured outcome, so the ruling that decides S1
# flips them deliberately rather than silently:
#
#   s1a  a closure at `includes` inside the module function: refused by gen-aspects' bare-closure
#        refusal when the element is read, 0 registrations.
#   s1c  a closure over a coordinate at a CLASS KEY inside the module function: delivered as a class
#        module — no lift, no registration, no refusal. Its `has` presence gate is dropped.
#   s1e  the same with a body reading the coordinate: fails in gen-merge naming a module argument,
#        never the door.
#
# Each carries its control: the same text OUTSIDE the module function, which is lowered.
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
  inherit (w) R merge aspects;
  keySemantics.nixos.category = "class";
  schema = aspects.mkAspectSchema { inherit keySemantics; };
  inner = { thimble, ... }: { description = "T-${thimble}"; };
  load = R.defunctionalize {
    cnf = {
      entityKinds = null;
      inherit keySemantics;
      inherit (w) moduleArgs;
    };
    declared = null;
    key = "s1:0";
    lambdasPath = [ "lambdas" ];
    aspectPaths = [ [ "aspects" ] ];
  };
  run =
    shape:
    let
      r = merge.evalModuleTree {
        modules = [
          { options.schema = schema.schemaOption; }
          (schema.mkAspectModule { })
          {
            options.lambdas = R.lambdas;
            config._module.args.pkgs = "PKGS";
          }
          (load shape)
        ];
      };
      m = r.config.aspects.main;
      try =
        v:
        let
          t = builtins.tryEval (builtins.deepSeq v v);
        in
        if t.success then t.value else "THROWS";
      shapeOf =
        x:
        if builtins.isFunction x then
          "lambda"
        else if builtins.isAttrs x then
          builtins.filter (
            k:
            builtins.elem k [
              "__guard"
              "__isWrappedFn"
              "__functor"
              "condition"
              "body"
            ]
          ) (builtins.attrNames x)
        else
          builtins.typeOf x;
    in
    {
      registrations = try (builtins.length (builtins.attrNames r.config.lambdas));
      includes = try (map shapeOf (m.includes or [ ]));
      classEval = try (
        if (m.nixos or null) == null then
          "no-class-content"
        else
          (merge.evalModuleTree {
            modules = [
              {
                options.marker = merge.mkOption {
                  type = merge.types.str;
                  default = "none";
                };
              }
              m.nixos
            ];
          }).config.marker
      );
    };
in
{
  flake.tests.s1-open-reading = {
    test-s1a-closure-in-includes-inside-a-module-function = {
      expr = {
        pinned = run { aspects.main = { config, ... }: { includes = [ inner ]; }; };
        control = run { aspects.main.includes = [ inner ]; };
      };
      expected = {
        pinned = {
          registrations = 0;
          includes = "THROWS";
          classEval = "no-class-content";
        };
        control = {
          registrations = 1;
          includes = [
            [
              "__guard"
              "body"
              "condition"
            ]
          ];
          classEval = "no-class-content";
        };
      };
    };

    test-s1c-class-key-closure-inside-a-module-function-is-silent = {
      expr = {
        pinned = run { aspects.main = { config, ... }: { nixos = { bobbin, ... }: { }; }; };
        control = run { aspects.main.nixos = { bobbin, ... }: { }; };
      };
      expected = {
        pinned = {
          registrations = 0;
          includes = [ ];
          classEval = "none";
        };
        control = {
          registrations = 1;
          includes = [
            [
              "__guard"
              "body"
              "condition"
            ]
          ];
          classEval = "none";
        };
      };
    };

    test-s1e-class-key-closure-reading-its-coordinate-fails-in-the-merge = {
      expr = {
        pinned = run {
          aspects.main = { config, ... }: { nixos = { bobbin, ... }: { marker = "u-${bobbin}"; }; };
        };
        control = run { aspects.main.nixos = { bobbin, ... }: { marker = "u-${bobbin}"; }; };
      };
      expected = {
        pinned = {
          registrations = 0;
          includes = [ ];
          classEval = "THROWS";
        };
        control = {
          registrations = 1;
          includes = [
            [
              "__guard"
              "body"
              "condition"
            ]
          ];
          classEval = "none";
        };
      };
    };
  };
}
