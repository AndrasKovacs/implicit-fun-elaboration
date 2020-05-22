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

See [benchmarks.fcif](benchmarks.fcif) here for an example file.

#### Differences to the paper

Extra features:
- Optional type annotations on lambdas, e.g. `λ (A : U). A`.
- Optional omission of type annotation on implicit binders and let,
   e.g. `let foo = U in foo` and `{A} → A → A`.
- Special treatment of top-level lambdas for the purpose of printing. These
  usually serve as a way of postulating constants. We don't print
  top-lambda-bound variables in meta spines in elaboration output and error
  messages, as they are irrelevant to meta solutions and would only add clutter.

Implementation:
- The metacontext is unordered in the implementation, unlike in the
  specification, where it is ordered. In principle, the metacontext as
  implemented can be ordered because the strengthening/occurs checking ensures
  that no cyclic dependencies are present in meta solutions and types.  This is
  a standard implementation strategy, also used in e.g. in Agda.
