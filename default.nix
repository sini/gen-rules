# Standalone (non-flake) entry — the L1 shim. Flake consumers should use the `.lib` output.
#
# THREE CHANNELS, ONE PRECEDENCE, AND NONE OF THEM IS A PROBE. A named formal per dependency wins;
# the `inputs` bag is next, tested by attrset membership so a supplied-but-throwing value throws as
# ITSELF rather than falling back; the default is resolved from `./flake.lock`, read as local data.
# There is NO `...`: an argument this root does not declare is a loud error, not a silent drop.
#
# THE PIN SOURCE IS THE ROOT `flake.lock`, NOT `ci/flake.lock` (ADR-0037 as amended 2026-09-15): a
# library's dependency graph and its test/oracle graph are SEPARATE.
#
# `src` AND `dep` ARE FORMALS, NOT `let` BINDINGS, AND THAT IS THE INJECTABLE RESOLVER SEAM. `src` is
# the only expression here that fetches; a caller supplying `src = segs: throw "…"` makes fetching
# IMPOSSIBLE for that application rather than merely absent.
#
# The `let` is OUTSIDE the lambda because a formal's default is evaluated in the FORMAL scope, which
# does not see a `let` in the body.
let
  lock = builtins.fromJSON (builtins.readFile ./flake.lock);
  # A direct edge IS the node key; a `follows` value is a PATH resolved segment by segment from this
  # lock's own root. It takes its lock as an argument, so a cell can drive this exact binding on a
  # fixture where the two rules disagree by construction.
  resolve =
    lock:
    let
      following =
        node: inp:
        let
          v = (lock.nodes.${node}.inputs or { }).${inp};
        in
        if builtins.isString v then v else builtins.foldl' following lock.root v;
    in
    segs: builtins.foldl' following lock.root segs;
  fetch = resolve lock;
in
{
  inputs ? { },
  src ? segs: "${builtins.fetchTree lock.nodes.${fetch segs}.locked}",
  # Arity dispatch, because a dependency's root is a function at a shim'd library and a bare value
  # at a leaf, and neither `import p` nor `import p { }` is total over both.
  dep ?
    segs:
    let
      v = import (src segs);
    in
    if builtins.isFunction v then v { } else v,
  # `wire` is the one channel that carries the formal-to-path map and the resolver OUT: a cell
  # injecting `dep = segs: segs` alongside `wire = args: args` reads both with nothing fetched.
  wire ?
    {
      deps,
      resolve,
      lock,
    }:
    import ./lib deps,
  prelude ? inputs.gen-prelude or (dep [ "gen-prelude" ]),
  scope ? inputs.gen-scope or (dep [ "gen-scope" ]),
  algebra ? inputs.gen-algebra or (dep [ "gen-algebra" ]),
  identity ? inputs.gen-identity or (dep [ "gen-identity" ]),
  # ★ A DEPENDENCY BUILT ON THE SUBSTRATE TAKES IT FROM ITS SIBLING FORMALS. `dep` would apply each
  # of these three to its OWN locked substrate and put a second gen-prelude, gen-scope, gen-algebra
  # or gen-merge instance in one evaluation; a formal's default may name a sibling formal, so each
  # default applies the member's root to THIS root's values instead. gen-program's root is
  # unapplied and takes all four; gen-merge and gen-aspects resolve their remaining inputs
  # (gen-types, gen-memo, gen-schema) from their own locks.
  merge ? inputs.gen-merge or (import (src [ "gen-merge" ]) { inherit prelude scope; }),
  program ?
    inputs.gen-program or (import (src [ "gen-program" ]) {
      inherit
        prelude
        scope
        algebra
        identity
        ;
    }),
  aspects ?
    inputs.gen-aspects or (import (src [ "gen-aspects" ]) {
      inherit
        prelude
        merge
        identity
        algebra
        ;
    }),
}:
# THE BODY IS EAGER: `forced` reaches every wired dependency's root VALUE (WHNF, never a member), so a
# default that cannot resolve is loud AT THE BOUNDARY rather than wherever a consumer first reaches
# an attribute.
let
  all = {
    inherit
      prelude
      scope
      algebra
      identity
      merge
      program
      aspects
      ;
  };
  deps = {
    inherit
      algebra
      identity
      aspects
      program
      merge
      ;
  };
  forced = builtins.deepSeq (builtins.mapAttrs (_: builtins.typeOf) all) null;
in
builtins.seq forced (wire {
  inherit deps resolve lock;
})
