## fcif

Implementation of the elaborator in the draft paper "Elaboration with
First-Class Implicit Function Types".

We also have here a small supplementary Agda file,
[TelescopeDerivation.agda](TelescopeDerivation.agda), which contains a derivation
of telescopes and curried functions from Section 4 of the paper.

#### Installation

- Install Haskell Stack: https://docs.haskellstack.org/en/stable/README/ if you don't already have it
- `stack install` from this directory
- This copies the executable `fcif` to `~/.local/bin`.
- Agda installation for checking the Agda file: see [Agda
  docs](https://agda.readthedocs.io/en/v2.6.0.1/getting-started/installation.html). A
  [standard library](https://github.com/agda/agda-stdlib) is also required.

#### Usage

The executable `fcif` reads an expression from standard input.

- `fcif elab` prints elaboration output.
- `fcif nf` prints the normal form of the input.
- `fcif type` prints the type of the input.

See [benchmarks.fcif](benchmarks.fcif) here for an example.

#### Comparison to the paper

Extra features:
- Optional type annotations on lambdas, e.g. `λ (A : U). A`.
- Optional omission of type annotation on implicit binders and let,
   e.g. `let foo = U in foo` and `{A} → A → A`.
- Special treatment of top-level lambdas for the purpose of printing. These
  usually serve as a way of postulating constants. We don't print
  top-lambda-bound variables in meta spines in elaboration output and error
  messages, as they are irrelevant to meta solutions and would only add clutter.

Differences:
- The metacontext is unordered in the implementation, unlike in the
  specification, where it is ordered. In principle, the metacontext as
  implemented can be ordered because the strengthening/occurs checking ensures
  that no cyclic dependencies are present in meta solutions and types.  This is
  a standard implementation strategy, also used e.g. in Agda.

Notation:
- Metavariables are printed as `?n`, where `n` is an integer, meaning
  the `n`-th fresh metavariable.
- Inserted binders which arise from curried function insertion are named `Γn`,
  where `n` is an integer. `n` isn't particularly informative, it comes from a
  combination of fresh meta ids and telescope refining.
- Non-unicode in surface syntax: lambdas can be written as
  `\` and `λ`, and function arrows as `->` and `→`.
- We print curried functions in the same way as implicit functions. They can be
  disambiguated visually by having a telescope domain.
- Curried lambdas are printed as `λ{x : a}. t` where `a` is a telescope.
- Curried applications are printed as `t {u : a}`, where `a` is a telescope.
