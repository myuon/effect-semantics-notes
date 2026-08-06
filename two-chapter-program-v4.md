# Two-chapter research program v4

## Status

**Adopted organization.**  The development is split into a finite shallow
chapter and a recursive deep chapter.  The split is methodological rather than
an assertion that recursion requires deep handlers.

## The two independent axes

There are two distinct choices:

| axis | finite side | stronger side |
|---|---|---|
| computation shape | recursion-free, well-founded | recursive or potentially infinite |
| handler scope | shallow, handles one exposed free request | deep, reinstalls itself on resumptions |

The main path studies the diagonal:

1. **Chapter I:** recursion-free language with the intended shallow matcher;
2. **Chapter II:** recursive language with exhaustive deep handlers.

This makes the mathematical development progressive, but every claim must say
which axis causes the change.  In particular:

- infinite domains, admissibility and fixed-point induction are caused by
  recursion;
- failure to eliminate all occurrences of an interface is caused by
  shallowness;
- multi-shot resource interaction is caused by resumption usage, not by
  recursion alone.

The off-diagonal combinations—finite/deep and recursive/shallow—remain useful
controls.  They prevent us from crediting deep handling with a theorem that
actually follows only from finiteness, or vice versa.

## Chapter I question

Fix a terminating base language and add finite first-order free operations.
The intended shallow construct:

1. evaluates through base computation until the first free request or return;
2. checks that single request against its interface;
3. on a match, computes one replacement response and resumes the captured tail
   exactly once;
4. does not reinstall itself around the tail;
5. on a different interface, forwards the request and terminates the matcher.

The chapter asks:

> Which operational, algebraic, relational and observational structures of the
> finite base language survive this extension, and which conclusions are
> impossible because the handler sees only one free boundary?

The construct is intentionally smaller than a first-class shallow handler: the
source branch has no continuation variable, so it cannot discard or duplicate
the continuation.  Those variants can be compared later, but they are not part
of the Chapter I theorem.

## Chapter I target result

The positive theorem should transport:

- deterministic decomposition;
- preservation and effect-aware progress;
- old-syntax operational conservativity;
- the finite free-tree monad and base embedding;
- operational/tree correspondence for the shallow matcher;
- lifting of base morphisms and compatible logical relations;
- ground adequacy at the observation level supplied by the base package.

It should not claim:

- complete removal of interface $\Delta$ from an unordered may-row;
- that the shallow matcher is a monad morphism;
- an exact transformed old base grade from the old grade and free row alone;
- handler commutation;
- any theorem about divergence.

## Chapter II question

Chapter II replaces well-founded trees by recursive resumptions and the
one-boundary matcher by a deep handler.  It then asks which Chapter I
certificates lift through:

- least fixed points, complete-Elgot iteration or guarded recursion;
- admissible logical relations;
- handler reinstallation;
- finite, divergence and productive-trace observation levels.

The important comparison is that deep handling can discharge an interface
from an unordered outward row, while recursion determines what proof principle
is needed to justify that discharge for infinite computations.

## Dependency rule

Chapter II may reuse Chapter I's syntax, finite approximants and local handler
equations.  It must not silently reuse Chapter I's normalization argument.
Conversely, Chapter I must not invoke recursive resumption machinery merely to
describe a finite shallow computation.
