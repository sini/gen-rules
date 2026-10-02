{
  inputs = {
    gen-harness.url = "github:sini/gen-harness";

    # nixpkgs is the CI runner's dependency (the nix-unit harness, treefmt) and supplies the `lib`
    # the test modules use. It enters ONLY in ci/, never as a `lib/` dep: the library is
    # nixpkgs-lib-free, which `ci/tests/purity.nix` enforces.
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";

    # ★ THE SUBSTRATE IS TAKEN DIRECTLY, NEVER THROUGH THE HUB. The hub pins this repository, so a
    # hub input here closes a cycle in the oracle graph (ADR-0037). The root flake's five
    # dependencies and the substrate under them, with the same `follows`, so the door, the aspects it
    # hands onward to and the program it fires into share one gen-merge, gen-algebra and gen-identity.
    gen-prelude.url = "github:sini/gen-prelude";
    gen-graph.url = "github:sini/gen-graph";
    gen-graph.inputs.gen-prelude.follows = "gen-prelude";
    gen-scope.url = "github:sini/gen-scope";
    gen-scope.inputs.gen-prelude.follows = "gen-prelude";
    gen-scope.inputs.gen-graph.follows = "gen-graph";
    gen-algebra.url = "github:sini/gen-algebra/18238b1c08d943dd7288b09e40c0b1d865e66d9d";
    gen-identity.url = "github:sini/gen-identity";
    gen-merge.url = "github:sini/gen-merge";
    gen-merge.inputs.gen-prelude.follows = "gen-prelude";
    gen-merge.inputs.gen-scope.follows = "gen-scope";
    gen-program.url = "github:sini/gen-program/04c91612c33aaa453c7c89a3f9204b8456ee28bd";
    gen-program.inputs.gen-prelude.follows = "gen-prelude";
    gen-program.inputs.gen-scope.follows = "gen-scope";
    gen-program.inputs.gen-algebra.follows = "gen-algebra";
    gen-program.inputs.gen-identity.follows = "gen-identity";
    gen-aspects.url = "github:sini/gen-aspects/1062acbeec6981ace3703f455db8eb2e45c719b9";
    gen-aspects.inputs.gen-prelude.follows = "gen-prelude";
    gen-aspects.inputs.gen-merge.follows = "gen-merge";
    gen-aspects.inputs.gen-identity.follows = "gen-identity";
    gen-aspects.inputs.gen-algebra.follows = "gen-algebra";
  };

  outputs =
    inputs@{
      gen-harness,
      ...
    }:
    let
      prelude = inputs.gen-prelude.lib;
      scope = inputs.gen-scope.lib;
      algebra = inputs.gen-algebra.lib;
      identity = inputs.gen-identity.lib;
      merge = inputs.gen-merge.lib;
      aspects = inputs.gen-aspects.lib;
      # The application the hub's `lib/hubSubstrate.nix` performs for `program`, and the ONE
      # gen-program instance this oracle holds: the door fires into it and the cells solve with it.
      program = inputs.gen-program.lib {
        inherit
          prelude
          scope
          algebra
          identity
          ;
      };
      genRules = import ../lib {
        inherit
          algebra
          identity
          aspects
          program
          merge
          ;
      };
    in
    gen-harness.lib.mkCi {
      inherit inputs;
      name = "gen-rules";
      testModules = ./tests;
      specialArgs = {
        inherit genRules;
        genAlgebra = algebra;
        genIdentity = identity;
        genAspects = aspects;
        genProgram = program;
        genMerge = merge;
        genPrelude = prelude;
      };
      # Cells whose subject is an error MESSAGE cannot live under `testModules`: the batch asserter
      # behind `checks.default` forces every `expr` UNCONDITIONALLY, so a cell with a throwing `expr`
      # CRASHES that gate instead of failing it. They get their own output, read by
      # `nix-unit --flake ./ci#testsError`.
      extraModules = [
        ./tests-error.nix
      ];
    };
}
