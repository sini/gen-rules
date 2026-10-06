# Module-function shapes at the door (den-hoag-zm0gu, den-hoag-d13lv). Two constructions:
#
#   zm0gu  a closure's OUTPUT that is (or holds) a module function is applied by the module system,
#          under arguments the door never holds: a closure in its result can be neither registered
#          nor scoped, so it is refused by name when applied, and a result holding none is served.
#   d13lv  a class-key closure over coordinates only (`nixos = { bobbin, ... }: …`) lifts to a module
#          the door admits, and fires as its module-argument control does.
#
# Each refusal cell reads the output downstream as an aspect definition in a fresh mounted aspect
# evaluation, the way gen-aspects receives a door node's value.
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
  attempt =
    v:
    let
      r = builtins.tryEval (builtins.deepSeq v v);
    in
    if r.success then r.value else "refused";
  cls = { bobbin, pkgs, ... }: { marker = "delivered"; };
  modfn = { config, ... }: { nixos = cls; };
  # the closure's output, fired at a context without `bobbin`
  fired =
    out:
    let
      f = m.framework { modules = [ { config.aspects.main.includes = [ out ]; } ]; };
    in
    f.fire { thimble = "x"; } (builtins.head (m.guardsIn f.r.config.aspects.main));
  down =
    o:
    let
      cnf0 = {
        entityKinds = null;
        keySemantics.nixos.category = "class";
        inherit (m.w) moduleArgs;
        aspectModules = [ (R.lambdasMount "lambdas") ];
      };
      schema = aspects.mkAspectSchema cnf0;
      p =
        (merge.evalModuleTree { } [
          { options.schema = schema.schemaOption; }
          (schema.mkAspectModule { })
          { config.aspects.probe = o; }
        ]).config.aspects.probe;
      inc = builtins.head (builtins.filter (x: !(m.isGuard x)) (p.includes or [ ]) ++ [ { } ]);
      cv = if (p.nixos or null) != null then p.nixos else inc.nixos or null;
    in
    attempt {
      doorNodes = builtins.length (m.guardsIn p);
      class = if cv == null then "absent" else m.classMarker cv;
    };
  run = cls': (m.run { modules = [ { aspects.main.nixos = cls'; } ]; }).fired;
  runIn =
    cls': (m.run { modules = [ { aspects.main = { config, ... }: { nixos = cls'; }; } ]; }).fired;
in
{
  flake.tests.module-fn-shapes = {
    # zm0gu, N1's shape: the class value is never delivered without its `has bobbin` guard.
    test-a-module-function-output-writing-a-class-closure-is-refused = {
      expr = down (fired ({ thimble, ... }: modfn));
      expected = "refused";
    };

    # zm0gu, the same mechanism one level down: a module function at an aspect position of an attrset
    # output.
    test-a-module-function-nested-in-an-attrset-output-is-refused = {
      expr = down (fired ({ thimble, ... }: { includes = [ modfn ]; }));
      expected = "refused";
    };

    # zm0gu control: a module-function output whose result holds no closure is served unchanged.
    test-a-module-function-output-holding-no-closure-is-served = {
      expr = down (
        fired (
          { thimble, ... }:
          { config, ... }:
          {
            nixos = { pkgs, ... }: { marker = "plain-${thimble}-${pkgs}"; };
          }
        )
      );
      expected = {
        doorNodes = 0;
        class = "plain-x-P";
      };
    };

    # zm0gu control: the check is lazy and positional, so a served class value that reads `config`
    # while the merge folds the module's declarations still reads its value.
    test-a-module-function-output-reading-config-at-a-class-key-is-served = {
      expr = down (
        fired (
          { thimble, ... }:
          { config, ... }:
          {
            nixos = if config ? nixos then { marker = "cfg"; } else { marker = "nocfg"; };
          }
        )
      );
      expected = {
        doorNodes = 0;
        class = "cfg";
      };
    };

    # zm0gu control at the nested position: a module function in an attrset output whose result holds
    # no closure is served.
    test-a-module-function-nested-in-an-attrset-output-holding-no-closure-is-served = {
      expr = down (
        fired (
          { thimble, ... }:
          {
            includes = [
              (
                { config, ... }:
                {
                  nixos = { pkgs, ... }: { marker = "np-${pkgs}"; };
                }
              )
            ];
          }
        )
      );
      expected = {
        doorNodes = 0;
        class = "np-P";
      };
    };

    # d13lv: a coordinate-only class closure fires, at the aspect and inside a module function, as its
    # module-argument control does.
    test-a-coordinate-only-class-closure-lifts-and-fires = {
      expr = {
        coordinateOnly = attempt (run ({ bobbin, ... }: { marker = "u-${bobbin}"; }));
        coordinateOnlyInModuleFn = attempt (runIn ({ bobbin, ... }: { marker = "u-${bobbin}"; }));
        control = attempt (run ({ bobbin, pkgs, ... }: { marker = "u-${bobbin}-${pkgs}"; }));
      };
      expected = {
        coordinateOnly = [ { nixos = "u-b"; } ];
        coordinateOnlyInModuleFn = [ { nixos = "u-b"; } ];
        control = [ { nixos = "u-b-P"; } ];
      };
    };
  };
}
