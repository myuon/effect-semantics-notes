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
- a separate affine shallow-handler machine with matching, bare-continuation
  resumption, and transparent base/nonmatching forwarding;
- partial handler lookup, an independent exhaustiveness predicate, local
  clause-typing certificates and checked parameter instantiation;
- executable `tick`/`tock` witnesses showing that matching removes the pending
  handler while a missing same-interface clause forwards and reinstalls it.
- renaming preservation for typed residual contexts, typed reconstruction of
  the bare continuation under a fresh response binder, and coarse affine-match
  preservation at `clauseEffect * oldResultEffect`.
- principal residual-effect reconstruction and ordered cancellation under a
  selected-interface-free prefix;
- the sharp affine law
  `pre * [free interface] * post ↦ pre * clauseEffect * post`;
- preservation of the two-phase handler-state invariant for internal, return,
  matching and all three typed forwarding/resumption cases.
- a concrete finite `WriterTree` with Writer and free nodes, checked monad
  laws, structural shallow-handler equations and executable nested examples;
- structural relation lifting through bind and shallow handling, naturality in
  the result carrier, and reflection of closed Writer observations.
- source-level Writer/tree adequacy as an equivalence between direct Writer
  runs and finite tree observations;
- finite Writer orthogonality and TT closure, structural-to-TT inclusion,
  shallow TT preservation and observation reflection;
- ordered grade indexing of Writer trees, graded bind/map and proof that every
  observed Writer trace is a subsequence of its declared grade.
- a response-type-indexed Writer/free carrier whose continuations accept only
  closed values of the operation's declared response type;
- typed source/tree production, typed Writer adequacy and grade soundness;
- typed shallow folds, structural relation/graph lifting, finite TT transport,
  and exact-grade exhaustive first-occurrence replacement;
- a checked counterexample showing naive first-occurrence replacement is not
  monotone under ordered-subsequence subeffecting, plus a finite sound
  replacement envelope for every subword.
- downward-closed trace languages with associative sequential product,
  principal-word embedding and a monotone language-level handler;
- language-graded typed Writer/free trees with graded bind/map and observation
  membership;
- concrete effect-algebra, typed Writer monad/adequacy and finite shallow
  certificate records populated entirely by proved declarations.
- finite State and Exception tree models with monad laws, base traversal,
  structural relation bind/shallow preservation and executable observations;
- common finite monad/relator/shallow-relator certificates instantiated by
  Writer, State and Exception;
- finite derived-deep approximants, composition, map/relation preservation,
  two-match convergence and the partial-handler non-elimination regression.
- production/run transport across alternative typing derivations and explicit
  effect weakening, so the operational correspondence is not tied to one
  proof-relevant derivation tree;
- generic renaming/substitution cancellation and the checked continuation
  identity `request.openResume.subst0 response = request.resume response`.
- operational `let`/tree-`bind` correspondence and the full untyped
  source-shallow/tree-shallow commutation theorem, including matching, Writer
  forwarding, cross-interface forwarding and missing-clause forwarding.

Typing derivations live in `Type` rather than `Prop`: this exposes the explicit
subeffecting derivation tree needed by the terminating mutual transformation.
The associated inhabitation proposition can later be proof-irrelevant even
though the checked certificate is retained as data.

Remaining work includes source-level handler/tree commutation and a genuine
recursive/domain model beyond finite approximants. No `sorry`
or project axiom is admitted in the checked library.
