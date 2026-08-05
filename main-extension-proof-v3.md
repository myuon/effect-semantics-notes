# Main extension proof v3

## Status

**Proof synthesis for the main extension theorem.**  This page records the
dependency of every conclusion and prevents the theorem statement from hiding
instance-specific assumptions.

## 1. Operational construction

Extend the base evaluation contexts with `let` and pending new handlers.  For a
fixed interface $\Delta$, the transparent context contains no intervening
$\Delta$ handler.

The four boundary cases are:

1. return;
2. old base outcome;
3. matching free request;
4. nonmatching free request.

Matching performs the clause step with a deep resumption.  Nonmatching forwards
the request and retains the pending handler in the response continuation.

## 2. Decomposition and determinism

Induct on the unique active CBV context.

- An old redex/outcome uses `BaseSafety`.
- A recursive application is an old deterministic unfolding redex.
- A free request has a unique nominal interface.
- The nearest matching handler is determined by the transparent-context
  decomposition.
- Matching and forwarding are disjoint.

This yields extended decomposition and relative determinism without reference
to denotation or normalization.

## 3. Preservation and discharge

Preservation is by cases on the step.

- Old steps use base preservation and new-row silence.
- Beta/unfolding use value and simultaneous recursive substitution.
- Handler return/matching use clause substitution and residual-context typing.
- Forwarding reconstructs the same residual row with the pending handler.

If a handled result has outward row $\omega$ with
$\Delta\notin\omega$, preservation maintains this fact at every reachable
state.  Progress would require any escaping request label to belong to
$\omega$, so an escaping $\Delta$ is impossible.

This proves deep discharge even for an infinite execution, because the argument
quantifies over each finite reachable state.

## 4. Recursive denotation

Interpret syntax compositionally in the supplied recursive resumption model.

- Old terms use the base embedding.
- `return` and `let` use the row monad.
- free operations use request constructors.
- recursive functions use the supplied iteration operator.
- a handler is the selected fixed point of its return/matching/forwarding/base-
  outcome functional.

Continuity/guardedness of the handler functional follows by typing induction on
language-defined clauses.  Target-row indexing gives semantic discharge.

## 5. One-step soundness

Induct on the reduction derivation.

- Old steps use base rule soundness.
- Beta, let-return, branches, and recursive unfolding use semantic
  substitution; recursive unfolding is the iteration unfolding law.
- Handler return/matching/forwarding use the corresponding fixed-point handler
  equation.
- Context closure uses bind and handler congruence.

No operational reflection is used in this direction.

## 6. Fundamental relation

Let $\mathcal V_A$ and $\mathcal C_A^\rho$ be the package's admissible/guarded
value and computation relations.  Relate closing substitutions pointwise.

Prove simultaneously:

$$
V[\gamma]\mathcal V_A\llbracket V\rrbracket\eta,
$$

$$
M[\gamma]\mathcal C_A^\rho\llbracket M\rrbracket\eta.
$$

Ordinary cases use relation compatibility.  Two cases contain the recursive
content.

### Recursive function

Relate the source recursive value to every finite semantic approximant, using
one source unfolding and the body induction hypothesis at the successor step.
Admissibility/guarded Löb induction passes to the selected fixed point.

### Deep handler

Define a predicate on candidate semantic handlers asserting preservation of
the computation relation.  Prove it at bottom/later and show it is preserved by
the handler functional using return, base outcome, matching, and forwarding
cases.  Fixed-point/guarded induction gives the selected handler.

This proves the generic fundamental theorem.

## 7. Adequacy extraction

For a closed term, instantiate the fundamental theorem with the empty
environment.

- A semantic finite boundary unfolds the computation relation and produces the
  corresponding operational boundary.
- A finite operational boundary gives the semantic boundary by one-step
  soundness.
- At a Level-2 empty/resolved row, if the only nonbottom constructors are
  classified finite outcomes, their absence plus deterministic decomposition
  characterizes boundary divergence.
- At Level 3, use the stronger coinductive observation relation supplied by the
  base; no Level-2 argument fabricates an infinite trace.

## 8. Conservativity proof

Induct on an old typing derivation.  Every constructor is interpreted through
the base embedding, which preserves return, bind, primitives, and iteration.
No free-request or new-handler clause occurs.  The operational result is
immediate from conservative syntax.

## 9. Morphism proof

Define $\widehat q$ through the recursive resumption's finite projections or
coalgebraic universal property, applying $q$ to each exposed base phase and
recursing/guarding through free requests.

Return, bind, weakening, and request preservation follow structurally.
Recursive terms use

$$
q(f^\dagger)=(qf)^\dagger.
$$

Handler compatibility follows because both composites solve the same mapped
handler functional with the package's selected fixed-point coherence.

## 10. Dependency table

| Conclusion | Safety | resumption/iteration | admissible relation | observation reflection | interaction law |
|---|---:|---:|---:|---:|---:|
| decomposition/determinism | yes | no | no | no | nominal handler scope |
| row preservation/progress | yes | no | no | no | no |
| deep discharge | yes | no | no | no | deep reinstallation |
| operational conservativity | yes | no | no | no | no |
| denotational embedding | no | yes | no | no | no |
| recursive handler | no | yes | no | no | handler functional |
| one-step soundness | yes | yes | no | primitive soundness | handler equations |
| finite adequacy | yes | yes | yes | Level 1 | related clauses |
| divergence adequacy | yes | yes | yes | Level 2 | strictness/guardedness |
| productive traces | yes | yes | guarded/coinductive | Level 3 | trace-visible handler |
| morphism lifting | no | yes | no | preservation | iteration compatibility |
| exact old base grade | insufficient | insufficient | insufficient | insufficient | extra abstraction law |

## 11. Proof boundary

The generic proof is complete at paper level relative to its packages.  A formal
proof must choose concrete encodings of:

- typed syntax and substitution;
- recursive domains or guarded trees;
- finite projections/step indices;
- admissibility/guarded relation;
- the selected fixed-point uniqueness/coherence principle.

The Writer, State, and Exception instances demonstrate consistency and
nonvacuity of the assumptions through Level 2.
