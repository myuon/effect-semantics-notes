# Scope, status, and open obligations

This part records what is *not* asserted by the mathematical statement pages.
It includes formalization status, conditional interfaces, missing
constructions, counterexample-driven repairs, future directions, and
historical decisions.

These records are not additional premises of the main theorems. They are kept
separate so that a reader can distinguish:

1. a proved theorem;
2. a paper-level packaging of proved components;
3. a valid conditional theorem awaiting an instance;
4. a conjectural statement still needing repair;
5. an obsolete or superseded design.

## Read this part from top to bottom

1. [Statement-to-Lean review map](review-guide.md) gives the concise status of
   each stable mathematical statement.
2. [Lean index](lean-api-reference.md) provides direct declaration lookup.
3. [Claim status and supersession ledger](claims-ledger.md) records which old
   formulations have been replaced.
4. [Open formalization obligations](formalization-gap-audit.md) retains only
   dependency-ordered gaps on the current proof path.
5. [Lean implementation roadmap](lean-formalization-roadmap-v5.md) explains
   the engineering order for closing those gaps.
6. [Quantitative catch handlers](quantitative-catch-handlers-direction.md) is a
   separate future direction and is not a premise of the current theorem.

The [work log](work-log.md) is historical provenance, not a source of current
mathematical truth. When it conflicts with a current statement or the claims
ledger, the current statement and ledger take precedence.
