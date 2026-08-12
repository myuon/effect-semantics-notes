# Formal setting and definitions

This part fixes the mathematical objects used by the theorem statements:
syntax, typing judgments, evaluation contexts, ordered effects, operational
models, denotational models, free extensions, handlers, and recursive
completion.

Definitions that have Lean counterparts retain a link beside the definition.
Such a link means that the displayed object or its explicitly identified
component is kernel checked. A definition without an exact Lean link should be
read according to its local status panel, usually as a paper abstraction or an
explicit hypothesis.

## Layering

1. [Objects and notation](objects-and-notation.md) fixes the common vocabulary.
2. Chapter I fixes the finite base calculus and its two semantic models.
3. Chapter II adds free operations and the finite/graded free carrier.
4. Chapter III adds shallow handlers.
5. Chapter IV adds recursion and derives deep handling.

This part answers “what are the objects?” Claims about those objects are
collected separately in [Theorem statements](theorem-statements.md).
