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
  # a plain third definition whose include condition throws: a raw unconditional fragment
  plainThrow = {
    key = "p";
    config.aspects.main.includes = merge.mkIf (throw "plain condition forced") [
      { description = "never"; }
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
  # fire `y`'s closure's door node alone, read from the coerced fragment's element
  fireInner =
    mods:
    let
      f = F mods;
      cf = builtins.head (builtins.filter (fr: fr.coerced or false) (carrierOf f).fragments);
    in
    (f.fire ctx (builtins.head (builtins.filter m.isGuard (builtins.head cf.body.includes).includes)))
    .description;
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

    # G5: a plain sibling's include condition is held raw, so firing `inner` does not force it
    test-g5-plain-sibling-condition-unforced = {
      expr = fireInner [
        x
        y
        plainThrow
      ];
      expected = "T-x";
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
  };
}
