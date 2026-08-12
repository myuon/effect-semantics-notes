# Proofs and dependencies

This part contains detailed derivations and reusable proof architecture. It is
separated from the statement pages so that the main results can be read without
interleaving every induction, admissibility argument, or dependency table.

Exact formal counterparts remain linked at the lemma or theorem where they are
used. The [Lean formalization index](lean-api-reference.md) provides the reverse
lookup from mathematical result to declaration.

## Read this part from top to bottom

1. The four chapter-proof pages follow the same order as the statement pages:
   base calculus, free extension, shallow handling, then recursion.
2. [Which theorem uses which assumption?](assumption-dependency-audit-v5.md)
   separates operational, carrier, monadic, relational, adequacy, and handler
   dependencies.
3. [Graded TT-lifting](graded-tt-lifting-v5.md) supplies the finite relational
   proof method.
4. [The non-circular observation pole](adequacy-pole-construction-v5.md)
   explains how adequacy follows without assuming the desired conclusion.
5. [Recursive TT-lifting](recursive-tt-audit-v5.md) adds admissibility and
   limits.
6. [The ordered-effect repair](effect-language-repair-v5.md) closes the proof
   story by replacing a non-monotone word operation with effect languages.

Proof sketches that merely orient the reader remain beside their theorem. Full
derivations and cross-cutting proof architecture belong here.

The remaining conditions and unfinished constructions are listed in [Scope,
status, and open obligations](scope-and-open-obligations.md).
