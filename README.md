# gen-rules

The one place in gen where a closure is applied. A framework's loader runs `defunctionalize` over
every module it admits, which turns each closure written at an aspect or rule position into a
first-order door node or door rule whose body is `ref r`, and registers the closure under `r`. The
door, `mkApply`, applies a registered closure to the context it is given, checks the output against
the codomain declared at registration, and hands onward data only. The catalogue holds the rule
patterns, which emit gen-program declarations and evaluate nothing.

## Why it exists

gen-aspects and gen-program hold terms only: a guard is a condition term and a body term, and a rule
body is a term. A framework's users still write closures (`{ thimble, ... }: { … }`), and those
closures have to cross into a first-order world somewhere. Without one crossing, every library that
meets a closure grows its own way of applying it, and nothing checks what comes back.

This library is that crossing, as Reynolds (1972, §6) describes defunctionalization: each closure
becomes a record tagged by its lambda, and one `apply` function interprets the records. The closure
is applied once, at the door, against exactly what its pattern reads:

- a formals pattern receives its formals;
- an open pattern receives the context restricted to the framework's declared coordinates;
- `{ }:` receives `{ }`.

Telling `{ }:` from `{ ... }:` and `x:` is the one place the library reads `builtins.toXML`, because
`functionArgs` is `{ }` for all three (`patternOf` in `lib/walk.nix`). **Option (c), not taken:** hand
every `functionArgs = { }` shape `{ }`. It is uniform and needs no `toXML`, but a `{ ... }:` closure is
then handed nothing it can read, and a bare positional `ctx:` aspect receives `{ }` too. At
`d933ba8`, 3 fixtures (`ci/tests/door.nix`, `ci/tests/lower.nix`) declare an open-pattern closure and
would change. **Flagged for owner review:** the `toXML` dependency.

## What it does

| intent                                   | export                                                                                            |
| ---------------------------------------- | ------------------------------------------------------------------------------------------------- |
| lower closures at the framework's loader | `defunctionalize { cnf; declared ? null; key; lambdasPath; aspectPaths ? [ ]; rulePaths ? [ ]; }` |
| declare the registration table           | `lambdas`, an option the framework mounts at `lambdasPath`                                        |
| mount the table inside each aspect       | `lambdasMount name`, a module the framework puts in `cnf.aspectModules`                           |
| build the door                           | `mkApply { lambdas; cnf; declared ? null; entityKinds ? null; }`                                  |
| write a conditional edge                 | `conditionalEdge { head; when; unless; relata; label ? null; }`                                   |
| write an abnormality                     | `abnormality { head; when; relata; }`                                                             |

**The lowering** is lazy and structure-preserving. At an aspect position, a context closure becomes a
door node `guard <cond> (ref r)`, where `<cond>` is `has` over the required formals, or `always` for an
open pattern. At a class key, a closure over declared coordinates is lifted into `includes`, while a
module function is the module slot and is carried unchanged. At a rule position, a closure becomes a
door rule carrying its declared contract (`emits`, `binds`, `suppresses`). Nothing is applied: a
top-level module function is wrapped by its formals and applied later by gen-merge.

**The door** returns `{ right = { output; scope; }; }` or a refusal value
`{ left = { code; witness; }; }`. It never throws. These are the refusal codes:

| code                         | when                                                                                         |
| ---------------------------- | -------------------------------------------------------------------------------------------- |
| `not-a-registration`         | the id is not refId's whole encoding (checked by length, then by grammar, before any decode) |
| `unregistered`               | the id is well-formed, but nothing is registered under its root                              |
| `source-rebound`             | a nested closure meets a coordinate from a different source than the one it was written for  |
| `required-coordinate-absent` | the door was called without a required formal                                                |
| `guard-codomain`             | a guard closure's output holds a function outside a class key or an aspect position          |
| `rule-codomain`              | a rule closure's output is not a list of declarations gen-program's rows know                |
| `codomain-breach`            | a fired declaration falls outside the declared `emits`/`binds`/`suppresses`                  |

A `null` contract field is the over-approximation and admits every name of that field. A closure
found inside an output becomes a nested door node, and its identifier records the outer closure and
the sources of the coordinates it received.

**The patterns** are Przymusinski's (1988, Example 9) pair. A `conditionalEdge` is
`head ← when, ¬unless`, and an `abnormality` is `unless ← trigger`. In the well-founded model an
edge whose condition holds is TRUE, an edge defeated by its abnormality is FALSE, and an edge whose
condition is absent is FALSE. `unless` is required; write `unless = null` for an edge that no
abnormality defeats.

## What it does not do, and does not claim

- **It checks nothing statically about a closure's body.** This is the stated price. The door checks
  each application's output, not the closure.
- **It does not enter a module function written at an aspect position at load.** The framework mounts
  the registration table inside gen-aspects' aspect submodule (`lambdasMount` in `cnf.aspectModules`,
  the one cnf handed to `mkAspectSchema`, `defunctionalize` and `mkApply`). The function is wrapped, and
  when gen-merge applies it, its result is lowered at the aspect it was written at and its closures
  register in that aspect's table. Each aspect's table is a definition of the root table, so the module
  system's own merge unites them and refuses a duplicate id by name. A loader over aspect positions
  without the mount is refused by name (`ci/tests/s1.nix`).
- **It does not serve a closure written in the result of a module function that a closure returned.**
  The door holds neither the module arguments that closure is created under nor a table to register
  it in, so it is refused by name when the module system applies the function. A result holding no
  closure is served (`ci/tests/module-fn-shapes.nix`).
- **It does not lower `__functor` aspects.** That form is the framework's vocabulary. A closure that
  returns one is refused by name.
- **It runs no head analysis.** The refusal for an over-approximated door rule (`null` binds or
  suppresses) belongs to the first analysis that reads heads, and no such analysis exists.
- **It solves nothing.** The patterns emit declarations; gen-program builds the program and
  gen-scope solves it.

## Running it

```sh
nix develop ./ci --command ci                # the suites, guarded against untracked cells
nix develop ./ci --command ci --tests-error  # the refusal messages
nix-unit --flake ./ci#tests 2>&1             # diagnostic: names each cell
```

`ci` refuses when anything under a declared read root is unknown to git. `git add` it, or move it.

## Naming

- `defunctionalize` and `mkApply` are Reynolds' terms: the transformation, and the one `apply`
  function that interprets its records.
- `lambdas` is the table `apply` interprets.
- `abnormality` is McCarthy's `ab`, as Przymusinski states it.
- `conditionalEdge` is the law's own term for the conditional inclusion it writes.
