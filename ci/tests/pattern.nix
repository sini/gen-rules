# The R4/R8 pattern reader, `lib/walk.nix` `patternOf`: walk's four kinds over gen-prelude's
# `patternOf` (den-hoag-gtwxg U2b). The reader is internal, so the cells import its unit file rather
# than adding an export for ci (ADR-0037).
{
  genAlgebra,
  genIdentity,
  genAspects,
  genMerge,
  genPrelude,
  ...
}:
let
  walk = import ../../lib/walk.nix {
    T = genAlgebra.term genIdentity.hashIdentity;
    aspects = genAspects;
    merge = genMerge;
    prelude = genPrelude;
  };
in
{
  flake.tests.pattern = {
    # A functor over a primop that publishes formals is read by those formals, closed: the formals
    # arm is tested before a primop maps to `unreadable` (den-hoag-gtwxg gate C5).
    test-functor-over-a-primop-with-formals-is-closed = {
      expr = walk.patternOf {
        __functor = self: builtins.map;
        __functionArgs = {
          a = false;
        };
      };
      expected = {
        kind = "formals";
        formals = {
          a = false;
        };
        closed = true;
        required = [ "a" ];
        reads = [ "a" ];
      };
    };
    # gen-prelude reads a pattern past any length of `@`-name (den-hoag-590wt), so an empty set
    # pattern whose 1100-character name pushes its head past prelude's prefix is read `empty`, as
    # walk's private regexes read it before the migration (den-hoag-gtwxg U2b).
    test-a-long-at-name-over-an-empty-set-is-empty = {
      expr = walk.patternOf (
        import (
          builtins.toFile "long-name.nix" "${
            builtins.concatStringsSep "" (builtins.genList (_: "x") 1100)
          }@{ }: 1"
        )
      );
      expected = {
        kind = "empty";
        formals = { };
        required = [ ];
        reads = [ ];
      };
    };
    # The control: the bare primop has no formals and neither pattern form.
    test-a-bare-primop-is-unreadable = {
      expr = walk.patternOf builtins.map;
      expected = {
        kind = "unreadable";
        formals = { };
        required = [ ];
        reads = [ ];
      };
    };
  };
}
