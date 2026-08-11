# Effect Semantics Lean formalization

The source grammar is indexed by `RecMode`. Chapters I–III use
`FinLanguageVal`/`FinLanguageComp`; Chapter IV uses
`RecLanguageVal`/`RecLanguageComp`. General recursion requires
`FixAllowed mode`, inhabited only at `.recursive`. The checked inclusion and
one-step simulation are in
`EffectSemantics.Metatheory.LanguageRecursionEmbedding`.

Pinned toolchain: Lean `v4.32.2`.

Build from this directory with:

```text
lake build
```

## Naming convention

Lean declarations are named for their mathematical role:

- `Structure` contains operations together with their defining laws;
- `Laws` contains equations or closure properties for an existing object;
- `Assumptions` contains premises consumed by a theorem;
- `Model`, `Metatheory`, and `Theory` bundle the corresponding semantic or
  syntactic results;
- `Package` is reserved for a genuine chapter-to-chapter interface combining
  several different kinds of data.

The former blanket `*Cert` suffix was removed because it did not distinguish
ordinary definitions such as a monad structure from discharged proof
obligations.

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
- a bundled Type-level functorial free-extension package, including
  identity/composition, bind naturality, exact graph lifting, structural
  relation closure, shallow compatibility, and finite adequacy transport;
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
  clause-typing packages and checked parameter instantiation;
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
  package records populated entirely by proved declarations.
- finite State and Exception tree models with monad laws, base traversal,
  structural relation bind/shallow preservation and executable observations;
- common finite monad/relator/shallow-relator packages instantiated by
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
- the response-type-indexed refinement of `let`/`bind` and shallow
  commutation, with explicit typed clause-model witnesses and checked
  matching-clause execution through `answerWith`.
- effectful recursive-function values with simultaneous argument/self
  substitution, unfolding, renaming/substitution preservation, one-step
  preservation and closed progress; a typed empty-effect self-loop carries an
  explicit infinite-reduction witness.
- stable fuel-indexed finite observations with a bottom element and
  approximation preorder; a recursive Writer observer accumulates `tell`
  output, reflects finite direct Writer runs, and maps the silent loop to
  bottom at every finite projection.
- an explicit ω-chain completion of finite observations, including least
  upper bounds, antisymmetry, ω-continuity, Kleene least fixed points, the
  unfolding equation and least-prefixed-point induction.
- a recursive deep Writer handler obtained by repeatedly reinstalling the
  direct shallow match; its fuel semantics is bidirectionally adequate for
  an inductive run relation, its limit is the union of finite observations,
  and that limit satisfies the handler functional's fixed-point equation.
- pointwise ω-chain suprema for whole-program Writer approximations, with a
  proof that the deep-handler functional preserves them; consequently the
  operational limit is its least pre-fixed point and least fixed point.
- admissible pole liftings for finite Writer observations and a reusable
  fixed-point induction theorem reducing recursive-handler logical-relation
  proofs to bottom and one-layer closure; the operational run pole supplies a
  checked instance.
- a typed recursive Writer adequacy endpoint: assuming operation `tell`
  returns unit and every installed affine clause is typed, every finite deep
  observation returns a closed value at the original computation result type,
  while intermediate effect bounds remain existential rather than falsely
  exact.
- an outward-boundary recursive Writer observer distinguishing return, base
  request and free request; for typed exhaustive handlers, every finite free
  boundary is proved different from the selected interface, giving a genuine
  semantic discharge theorem rather than hiding requests as bottom.

Typing derivations live in `Type` rather than `Prop`: this exposes the explicit
subeffecting derivation tree needed by the terminating mutual transformation.
The associated inhabitation proposition can later be proof-irrelevant even
though the checked package is retained as data.

The outward-boundary observer is stable under increasing fuel.  The reusable
finite-observation CPO infrastructure is polymorphic in its outcome: arbitrary
stable observations have bottom, antisymmetric approximation, ω-chain
suprema, continuous endofunctions and Kleene least fixed points.  The outward
Writer boundary has a witness-reflecting limit whose selected interface is
discharged.

Its type-indexed boundary relation covers return, outward base and outward
free observations, is admissible as an observation pole, and satisfies both
closed and open fundamental theorems under every typed closing substitution.
Recursive-function cases are included through the mechanized substitution
and preservation lemmas.

Generic recursive transport is now checked: an outcome map commuting with one
unfolding commutes with the two Kleene least fixed points, and any binary
admissible relation containing bottom and preserved by one unfolding relates
the two least fixed points.

- direct recursive operational boundary runs cover return, internal steps,
  Writer output, matched requests, old-base escape, cross-interface escape and
  missing-clause escape; this relation is equivalent both to a finite fuel
  observation and to the completed outward-boundary limit.
- the same generic observation completion now supports a recursive Exception
  instance: operation zero raises abortively, return/raise/base/free boundaries
  are separated, finite runs are adequate and deterministic, and exhaustive
  typed handlers discharge their selected interface.
- a recursive Boolean-State instance threads the current state through `get`,
  changes it at `put`, preserves it across free-handler matching, and exposes
  residual base/free boundaries with their state; its stable-limit adequacy,
  determinism and typed exhaustive discharge are checked.
- `RecursiveBoundaryModel` isolates the common assumptions to a fuel observer,
  stability, a direct run relation and finite adequacy.  Generic completion,
  limit adequacy, run determinism and the bottom/no-boundary characterization
  are derived; Writer, State and Exception inhabit the record.
- `RecursiveDischarge` makes the additional good-term and outward-interface
  conditions explicit and is instantiated from typedness, exhaustiveness and
  the Writer/State/Exception response laws.
- `RecursiveMorphism` and `RecursiveRelation` expose continuity,
  one-layer commutation/preservation, binary admissibility and bottom as
  separate fields; their fixed-point transport theorems are derived.
- outcome mapping satisfies identity and composition, its graph relation is
  binary admissible, and every recursive morphism package induces the
  corresponding relation package; graph and morphism lifting agree at
  the least fixed point.
- a concrete nonidentity instance erases Writer logs while retaining returned
  values; it commutes with one deep-handler unfolding, every finite
  approximant and the completed recursive fixed point.
- State and Exception now have their own type-indexed return/base/free
  boundary relations (plus typed `raise` for Exception), admissible poles and
  closed/open fundamental theorems under typed closing substitutions, matching
  the previously completed Writer proof chain.
- old-language syntax is characterized by a recursive `BaseOnly` predicate;
  it is preserved by renaming, arbitrary substitution, recursive self/argument
  substitution, one internal step and finite multistep evaluation, which can
  therefore never expose a newly added free request.
- every finite Writer behavior produced by a `BaseOnly` source has no free
  node, and structural shallow handling is exactly the identity on such a
  tree, giving denotational as well as operational conservativity.
- finite ordered words cannot satisfy `[atom]·e ≤ e`, formally exposing the
  obstruction to unrestricted effectful recursion; the downward-closed
  repetition language `atom*` contains pure behavior and does satisfy
  `[atom]·atom* ≤ atom*`.

Remaining work is now the audit and concrete instantiation of generic
source/tree transport premises. The recursive model, discharge, morphism and
relation package boundaries themselves are now machine checked.
No `sorry`
or project axiom is admitted in the checked library.
