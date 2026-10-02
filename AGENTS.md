# gen-rules — agent sheet

The framework-stratum library that holds **the only closure crossing in gen**: the loader lowering
(`defunctionalize`), the door that applies a registered closure (`mkApply`), and the rule-pattern
catalogue (`conditionalEdge`, `abnormality`). Read this before changing an export or calling one
from another repository.

## Scope

- **In:** lowering closures at a framework's loader into door nodes and door rules; the registration
  table; applying a registered closure at a context under 0cmbt R4/R8 (formals receive their formals,
  an open pattern receives `D`, narrowed to `E`); the two codomain contracts (guard, rule); nested
  closures and their identifiers; the two patterns.
- **Out, and who does it:**
  - holding and firing guards is gen-aspects (`mkGuardVocab`, `applyGuardWith`; the door reaches it as
    `cnf.ref`);
  - grounding and firing rules is gen-program (`groundInstances`, which takes the door as its `door`
    argument);
  - the rule contract's row table is gen-program's `codomainBreaches`;
  - solving is gen-scope;
  - the term algebra and `refId` are gen-algebra's;
  - minting is gen-identity's.

## The published surface

`import ./lib { algebra; identity; aspects; program; merge; }`, each APPLIED (`program` is gen-program
applied to its substrate). The root is published **UNAPPLIED** (`flake.nix`: `lib = import ./.;`); the
hub applies it through `gen/lib/hubSubstrate.nix`.

```json
["abnormality", "conditionalEdge", "defunctionalize", "lambdas", "mkApply"]
```

`ci/tests/surface.nix` asserts that list.

## Exports by intent

| intent                                    | export                           | file                      |
| ----------------------------------------- | -------------------------------- | ------------------------- |
| lower at the loader                       | `defunctionalize`                | `lib/defunctionalize.nix` |
| declare the table                         | `lambdas`                        | `lib/defunctionalize.nix` |
| build the door                            | `mkApply`                        | `lib/apply.nix`           |
| write a conditional edge / an abnormality | `conditionalEdge`, `abnormality` | `lib/catalogue.nix`       |

Internal: `lib/walk.nix`, the one traversal shared by the loader and the door. It returns
`{ value; found; bad; }`, three lazy fields over one child walk. It also holds the R4/R8 pattern
reader, `patternOf`.

## Entry points by task

- **Wire a framework:** mount `lambdas` at a path you choose. Pass every admitted module through
  `defunctionalize`, giving `aspectPaths` and `rulePaths` from your vocabulary map. Build
  `mkApply { lambdas = <merged table>; cnf; declared; }` and hand it to gen-aspects as `cnf.ref` and to
  gen-program's `groundInstances` as `door`. `ci/tests/_fixtures/world.nix` is a complete minimal
  framework.
- **Add a refusal:** return `refuse "<code>" { …; message; }` from `mkApply` (`lib/apply.nix`). Add a
  cell reading its code in `ci/tests/door.nix`. Name the plant that removes the refusal.
- **Add a pattern:** follow the pattern contract in `lib/catalogue.nix`: one record, every field
  checked by name, conditions as terms, gen-program declarations out, nothing evaluated. Add a
  gen-demo declaration.

## Measured traps

<!-- gen-citations:begin -->

- **`builtins.fromJSON` aborts uncatchably on malformed input, and `builtins.match` overflows the C++
  stack on a long subject.** The door's identify step therefore bounds the length (8192) and matches
  refId's whole grammar (`rxDeclared`, `rxNested` in `lib/apply.nix`) before any decode. A prefix
  match aborts on `{"declared":` (`ci/tests/door.nix`, `test-door-not-a-registration`).
- **The aspect's attribute set must never depend on a class value.** A lifted class key keeps its name
  with value `{ }`, and an aspect with a class key always carries `includes`. Removing the key made
  `attrNames` force every class value (`test-lower-lazy-class-values`).
- **A `#` inside a string literal blinds the purity scan's comment strip.** The inline-import key
  separator is spelled by its code point (`anonImport` in `lib/defunctionalize.nix`).
- **A top-level module function is wrapped by its formals**, so gen-merge must apply a functor module
  by its published formals. gen-merge before that change aborts with
  `called without required argument 'pkgs'` (`test-lower-module-fn-wrapped`).

<!-- gen-citations:end -->

## Theory

- Reynolds 1972, *Definitional Interpreters for Higher-Order Programming Languages*, §6:
  defunctionalization; the one `apply` function.
- Przymusinski 1988, Example 9: McCarthy's abnormality pair; an absent atom is FALSE in the
  well-founded model (ADR-0020).

## Tests

`nix develop ./ci --command ci` (the suites under `ci/tests/`) and
`nix develop ./ci --command ci --tests-error` (the refusal messages in `ci/tests-error.nix`).
