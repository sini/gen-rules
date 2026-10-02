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
  };
}
