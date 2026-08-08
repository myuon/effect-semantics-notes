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
- extrinsic typing, including latent arrow effects and subeffecting;
- capture-avoiding de Bruijn renaming/substitution functions;
- CBV `let` evaluation contexts, internal reductions and exposed base/free
  request records whose continuations are reconstructed from contexts.

The next proof obligation is the simultaneous value/computation renaming and
substitution theorem.  Because lambda bodies make the typing judgments
mutually inductive, it will be proved with their generated mutual recursor,
then used for one-step preservation and request-context typing.  No `sorry` or
project axiom is admitted in the checked library.
