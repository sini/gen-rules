# gen-rules — the one closure door, its loader lowering, and the rule-pattern catalogue.
#
# THREE PARTS, ONE OF WHICH APPLIES A CLOSURE.
#   defunctionalize  the lowering: a closure written to the framework's surface becomes a first-order
#                    door node or door rule whose body is `ref r`, and the closure is registered under
#                    `r` (Reynolds 1972 §6: a closure becomes a record tagged by its lambda expression)
#   mkApply          the door: Reynolds' one `apply` function over the registered lambdas. The ONLY
#                    place in gen a closure is applied. It hands onward data only.
#   catalogue        patterns: constructors that emit gen-program declarations; they evaluate nothing.
#
# L2: the dependency values are REQUIRED and arrive applied. `../default.nix` is the L1 shim that
# defaults them from the root lock; the hub supplies them from its own bindings. The library is
# nixpkgs-lib-free: the registration table's module-system vocabulary is gen-merge's
# (`merge.mkOption`, `merge.mkMerge`), never `lib.mkOption` (`ci/tests/purity.nix`).
{
  algebra,
  identity,
  aspects,
  program,
  merge,
}:
let
  T = algebra.term identity.hashIdentity;
  walk = import ./walk.nix { inherit T aspects merge; };
  door = import ./apply.nix {
    inherit
      T
      aspects
      program
      walk
      ;
  };
  loader = import ./defunctionalize.nix {
    inherit
      T
      aspects
      merge
      walk
      ;
  };
  catalogue = import ./catalogue.nix { inherit T; };
in
{
  inherit (loader) defunctionalize lambdas lambdasMount;
  inherit (door) mkApply;
  inherit (catalogue) conditionalEdge abnormality;
}
