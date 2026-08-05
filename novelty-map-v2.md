# Novelty map v2

## Status

**Superseded as the current audit.** See [Main theorem v3: novelty audit](novelty-audit-main-theorem-v3.md)
and [Research position after the v3 audit](research-position-after-audit-v3.md).
This page is retained as the pre-audit hypothesis map.

## What is already standard

The following cannot by themselves be novelty claims:

- user-defined first-order algebraic operations;
- unordered effect sets or rows;
- exhaustive deep handlers;
- handler elimination from an outward effect row;
- free-monad or interaction-tree semantics;
- handlers as folds or homomorphisms from free algebras;
- adding an algebraic signature through a free monad transformer;
- graded or category-graded effects and handlers in isolation.

Representative starting points include Plotkin and Pretnar on handling algebraic effects, Eff and core Eff, Koka and Links on row-typed effects, Frank, Flix, Unison, Effekt, work on category-graded algebraic theories, and abstract effect algebras for handler safety.

## Closest general frameworks to audit

| Work family | Likely overlap | Question for our project |
|---|---|---|
| algebraic effects and free models | deep handler as homomorphism | does it parameterize an already graded operational and denotational base package? |
| free monad transformers | adding a signature to an arbitrary monad | which conservativity, adequacy, and relation-preservation results are packaged? |
| row-typed handler calculi | unordered may-effects and elimination | do they separate a pre-existing base effect algebra from new free rows? |
| abstract effect algebras | generic type-and-effect safety | does the abstraction cover semantic and observational property preservation? |
| category-graded handlers | fine-grained grades, semantics, adequacy | how are old base semantics embedded, and what handler/base interactions are assumed? |
| higher-order effect frameworks | scoped and non-algebraic effects | where does first-order extension provably stop? |

## Candidate contribution gaps

The strongest current candidates are:

1. **Property-preserving extension as the primary object.** Treat operational semantics, denotation, observations, morphisms, and logical relations as input certificates to be transported.
2. **Capability-indexed handler hierarchy.** Relate one-shot, deep single-resumption, multi-shot, and higher-order handlers to minimal base assumptions.
3. **Ordered base with unordered new effects.** Analyze base-effectful clauses when the base grade is noncommutative but the public free-effect annotation is a row.
4. **Precision ladder.** Relate interaction trees, ordered traces, occurrence counts, and unordered rows by sound abstraction of handler action.
5. **Boundary theorems.** Give small counterexamples showing that opaque monads, multi-shot resumptions, or unordered rows lack specific information required by stronger preservation claims.

None of these is yet confirmed novel.

## Stop/go rule before a paper claim

Before promoting a candidate theorem to the main contribution:

1. state it with all assumptions;
2. search for the same input/output theorem, not merely the same language feature;
3. instantiate the closest abstract frameworks and see whether the theorem follows mechanically;
4. compare preservation results, not just syntax and type safety;
5. retain the claim only if there is a genuine missing theorem, weaker assumptions, stronger conclusion, or clarifying impossibility result.

## Current provisional positioning

The project is not currently positioned as a new effect-handler language.  Its provisional position is:

> a semantic audit of when an existing effectful language admits a conservative user-defined-operation and handler extension, organized by handler strength and the information retained by its effect abstraction.
