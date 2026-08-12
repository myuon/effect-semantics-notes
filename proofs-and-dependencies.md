# Proofs and dependencies

This part contains detailed derivations and reusable proof architecture. It is
separated from the statement pages so that the main results can be read without
interleaving every induction, admissibility argument, or dependency table.

Exact formal counterparts remain linked at the lemma or theorem where they are
used. The [Lean formalization index](lean-api-reference.md) provides the reverse
lookup from mathematical result to declaration.

## Contents

- chapter-specific proof details for substitution, preservation,
  conservativity, handlers, and recursion;
- the assumption dependency audit;
- graded TT-lifting and the non-circular adequacy pole construction;
- the ordered-effect repair explaining why downward-closed effect languages
  are needed.

Proof sketches that merely orient the reader remain beside their theorem. Full
derivations and cross-cutting proof architecture belong here.
