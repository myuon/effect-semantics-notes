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

## Read this part from top to bottom

1. [Objects and notation](objects-and-notation.md) fixes the common vocabulary.
2. [Finite base calculus](chapter-1-foundations-v5.md) defines syntax, typing,
   evaluation contexts, and internal reduction.
3. [Base semantics](chapter-1-denotational-v5.md) gives operational and
   denotational models for that calculus.
4. [Free-operation calculus](chapter-2-free-operations-v5.md) and
   [free-operation semantics](chapter-2-denotational-v5.md) add requests and
   their semantic carrier.
5. The graded FreeT pages then separate carrier existence, the concrete
   grade-indexed representation, and the base action required for bind.
6. [Shallow-handler calculus](chapter-3-shallow-handlers-v5.md) is followed by
   its [tree semantics](chapter-3-denotational-v5.md).
7. [Recursive calculus](chapter-4-fixpoint-derived-deep-v5.md) is followed by
   its [least-fixed-point semantics](chapter-4-denotational-v5.md).
8. [Why operational and denotational models remain
   separate](operational-denotational-comparison-v1.md) closes the part by
   relating the two semantic roles used throughout.

This part answers “what are the objects?” Claims about those objects are
collected separately in [Theorem statements](theorem-statements.md).
