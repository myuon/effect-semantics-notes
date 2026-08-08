# Effect Semantics Lean formalization

Pinned toolchain: Lean `v4.32.2`.

Build from this directory with:

```text
lake build
```

## Current boundary

Implemented and kernel-checked:

- ordered effect words and subsequence subeffecting;
- monoid, monotonicity, optional-interface insertion and empty-bound lemmas;
- typed base/free signatures with lookup uniqueness;
- fine-grain value/computation syntax in which source operations have no
  continuation argument;
- extrinsic, proof-relevant typing derivations, including latent arrow effects
  and subeffecting;
- capture-avoiding de Bruijn renaming/substitution functions;
- simultaneous value/computation renaming and substitution preservation,
  including substitution under binders and closed-value substitution;
- CBV `let` evaluation contexts, internal reductions and exposed base/free
  request records whose continuations are reconstructed from contexts.
- canonical return inversion through arbitrary outer subeffecting;
- one-step preservation for every internal reduction rule;
- typed evaluation contexts, plugging preservation and typed reconstruction of
  exposed free requests.
- converse plugging decomposition and reconstruction of typed residual
  contexts;
- request-grade factorization
  `[free interface] * suffix ≤ declaredEffect`;
- interface-free-bound safety under the concrete no-erasure preorder;
- closed progress into return/internal/base/free boundaries and deterministic
  internal stepping.

Typing derivations live in `Type` rather than `Prop`: this exposes the explicit
subeffecting derivation tree needed by the terminating mutual transformation.
The associated inhabitation proposition can later be proof-irrelevant even
though the checked certificate is retained as data.

The next layer is partial shallow handling: source syntax, matching and
transparent forwarding, handler preservation, and the `tick`/`tock`
counterexample. No `sorry` or project axiom is admitted in the checked library.
