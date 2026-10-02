{
  description = "gen-rules — the one closure door: the loader lowering that turns a closure into a first-order door node or door rule, the door that applies it, and the rule-pattern catalogue";

  # DECLARED, NOT APPLIED (owner-ruled Arm A, 2026-09-16). The library takes its substrate as INJECTED
  # VALUES constructed inside the consumer's own evaluation, and declaring an input is not applying
  # one. The declaration buys a ROOT LOCK, so the standalone entry (`default.nix`) has a pin source
  # that is not `ci/flake.lock` (ADR-0037 as amended 2026-09-15).
  #
  # ★ FIVE DEPENDENCIES, EVERY ONE POINTING DOWN OR WITHIN THE STRATUM. `gen-algebra` (the term
  # algebra and `refId`), `gen-aspects` (the door node's constructor and the lowering's one
  # classification surface), `gen-program` (the rule contract's row table, within the framework
  # stratum), `gen-identity` (the one minting authority the algebra is applied to) and `gen-merge`
  # (the registration table is a module-system option). The `follows` put all five on one
  # gen-prelude, gen-scope, gen-algebra, gen-identity and gen-merge, so the door, the aspects it
  # hands onward to and the program it fires into share one substrate.
  #
  # The test runner lives in ./ci, which is a separate flake.
  #
  # ★ THE FLAKE OUTPUT IS THE ROOT, PUBLISHED UNAPPLIED. The hub applies this output to its own
  # bindings (`gen/lib/hubSubstrate.nix`), so an APPLIED output here would abort every hub
  # evaluation with `attempt to call something which is not a function but a set`.
  inputs = {
    gen-prelude.url = "github:sini/gen-prelude";

    gen-graph.url = "github:sini/gen-graph";
    gen-graph.inputs.gen-prelude.follows = "gen-prelude";

    gen-scope.url = "github:sini/gen-scope";
    gen-scope.inputs.gen-prelude.follows = "gen-prelude";
    gen-scope.inputs.gen-graph.follows = "gen-graph";

    gen-algebra.url = "github:sini/gen-algebra/genrules-u1";
    gen-identity.url = "github:sini/gen-identity";

    gen-merge.url = "github:sini/gen-merge";
    gen-merge.inputs.gen-prelude.follows = "gen-prelude";
    gen-merge.inputs.gen-scope.follows = "gen-scope";

    gen-program.url = "github:sini/gen-program/genrules-u3";
    gen-program.inputs.gen-prelude.follows = "gen-prelude";
    gen-program.inputs.gen-scope.follows = "gen-scope";
    gen-program.inputs.gen-algebra.follows = "gen-algebra";
    gen-program.inputs.gen-identity.follows = "gen-identity";

    gen-aspects.url = "github:sini/gen-aspects/genrules-u2";
    gen-aspects.inputs.gen-prelude.follows = "gen-prelude";
    gen-aspects.inputs.gen-merge.follows = "gen-merge";
    gen-aspects.inputs.gen-identity.follows = "gen-identity";
    gen-aspects.inputs.gen-algebra.follows = "gen-algebra";
  };

  outputs = _: {
    lib = import ./.;
  };
}
