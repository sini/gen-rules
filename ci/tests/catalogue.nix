# UC1 (a door reference only as a whole body) and THE CATALOGUE: `conditionalEdge` and `abnormality`,
# Przymusinski 1988 Example 9's pair, lowered by gen-program's literal tier and solved in the
# well-founded model.
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
    t
    framework
    tuck
    ctx
    srcs
    throws
    program
    ;
  shapes = framework { modules = [ { fw.aspects.formals = tuck; } ]; };
  rule = framework { modules = [ { fw.rules.p = { thimble, ... }: [ ]; } ]; };
  outer = framework {
    modules = [
      {
        fw.aspects.outer =
          { thimble, ... }:
          {
            includes = [ ({ spool, ... }: { description = "inner-${spool}"; }) ];
          };
      }
    ];
  };
  outerOut =
    (outer.door {
      id = (outer.node "outer").body.id;
      context = ctx;
      sources = srcs;
    }).right;

  decl =
    d:
    program.declaration (removeAttrs d [
      "head"
      "relata"
    ]) (d.relata or [ "bolt" ]) d.head;
  solve =
    decls:
    program.model {
      program = program.program [ "bolt" ] decls;
      interpretation = [ ];
      prior = null;
      complete = true;
    };
  truth =
    m: a:
    if builtins.elem a m.trueAtoms then
      "T"
    else if builtins.elem a m.falseAtoms then
      "F"
    else if builtins.elem a m.undefinedAtoms then
      "U"
    else
      "absent-from-model";
  pats =
    cond: ab:
    R.conditionalEdge {
      head = "edge:bolt";
      when = t.has cond;
      unless = "ab:bolt";
      relata = [ "bolt" ];
      label = "to";
    }
    ++ (
      if ab then
        R.abnormality {
          head = "ab:bolt";
          when = t.has "trigger:bolt";
          relata = [ "bolt" ];
        }
      else
        [ ]
    );
  facts = map (h: {
    head = h;
    relata = [ "bolt" ];
  });
in
{
  flake.tests.catalogue = {
    # Every door node, door rule and nested node the walk emits has the body `ref r` and nothing else.
    test-uc1-ref-whole-body = {
      expr = {
        guard = (shapes.node "formals").body.__bodyTerm;
        rule = rule.config.rules.p.body.__bodyTerm;
        nested = (builtins.head outerOut.output.includes).body.__bodyTerm;
      };
      expected = {
        guard = "Ref";
        rule = "Ref";
        nested = "Ref";
      };
    };

    # `head ← when, ¬unless` and `unless ← trigger`, as positive and negative literals.
    test-pattern-lowers = {
      expr = map (d: { inherit (d) pos neg; }) (map decl (pats "cond:bolt" true));
      expected = [
        {
          pos = [ "cond:bolt" ];
          neg = [ "ab:bolt" ];
        }
        {
          pos = [ "trigger:bolt" ];
          neg = [ ];
        }
      ];
    };

    # Held with its condition, defeated by the abnormality, FALSE with its condition absent.
    test-pattern-model = {
      expr = {
        held = truth (solve (facts [ "cond:bolt" ] ++ pats "cond:bolt" true)) "edge:bolt";
        defeated = truth (solve (
          facts [
            "cond:bolt"
            "trigger:bolt"
          ]
          ++ pats "cond:bolt" true
        )) "edge:bolt";
        absentCond = truth (solve (pats "cond:bolt" true)) "edge:bolt";
      };
      expected = {
        held = "T";
        defeated = "F";
        absentCond = "F";
      };
    };

    # `unless` is required; `unless = null` is written for an edge no abnormality defeats.
    test-pattern-unless-required = {
      expr = {
        omitted = throws (
          R.conditionalEdge {
            head = "e";
            when = t.always;
            relata = [ "bolt" ];
          }
        );
        written = builtins.length (
          R.conditionalEdge {
            head = "e";
            when = t.always;
            unless = null;
            relata = [ "bolt" ];
          }
        );
      };
      expected = {
        omitted = true;
        written = 1;
      };
    };

    test-pattern-when-function-refused = {
      expr = {
        lambda = throws (
          R.conditionalEdge {
            head = "e";
            when = _: true;
            unless = null;
            relata = [ "bolt" ];
          }
        );
        term = builtins.length (
          R.conditionalEdge {
            head = "e";
            when = t.always;
            unless = null;
            relata = [ "bolt" ];
          }
        );
      };
      expected = {
        lambda = true;
        term = 1;
      };
    };
  };
}
