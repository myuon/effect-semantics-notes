# Ordered-trace research program v5

## Status

**Current research spine.**  This page supersedes the two-chapter diagonal of
v4.  The development now adds one construct at a time:

1. a fixed base language and ordered-effect vocabulary;
2. user-defined free operations;
3. shallow handlers;
4. computation-level fixed points;
5. deep handlers *derived* from shallow handlers and fixed points.

The purpose is still to determine how far an existing effectful language can
be extended while preserving its operational, denotational and observational
structure.  The changed premise is that effects retain execution order.

## Chapter structure

| chapter | new material | principal question |
|---|---|---|
| I | terminology, CBV syntax, base effects | what is fixed before extension? |
| II | free operation interfaces and ordered trace extension | is the extension conservative and compositional? |
| III | shallow handlers | how does one exposed operation transform a trace? |
| IV | fixed points and derived deep handlers | which finite results survive recursion, and when does recursive reinstallation discharge an interface? |

The chapters are cumulative.  In particular, Chapter IV does not introduce a
second primitive handler calculus.

## Ordered effects

Let the base effect algebra be a preordered monoid

$$
(B,\cdot,1,\leq).
$$

An individual run has an ordered trace.  A static annotation denotes a
language of possible traces, because a type system must also describe
conditionals and other unresolved choices.  Concatenation models sequencing
and language union models control-flow join.  Thus order is retained without
claiming that type checking predicts one unique runtime path.

After adding interfaces $\Delta\in\mathcal D$, traces are reduced words in the
free product

$$
\widehat E = B * \mathcal D^*.
$$

We use

$$
b\cdot\Delta\cdot e
$$

as a singleton-trace shorthand, or as a schematic member of a trace language.
It says that a base segment $b$ precedes a $\Delta$ request and residual trace
$e$.  It is not the unordered assertion that all three labels may occur.

## Guiding shallow equation

For the affine response fragment, suppose a $\Delta$ clause has trace $e'$ and
supplies exactly one response to the captured tail.  The intended effect
transformation is

$$
b\cdot\Delta\cdot e
\longmapsto
b\cdot e'\cdot e.
\tag{Trace-Shallow}
$$

The prefix $b$ has already happened, the exposed request is replaced by the
clause computation, and the continuation retains $e$.  On a trace language,
the transformer acts pathwise; joins remain joins.

This equation is exact only for the affine response fragment.  A general
shallow clause receives the continuation and may discard or duplicate it.  Its
effect transformer must therefore account for continuation usage.

## Why shallow syntax exposes a continuation

Chapter III adopts the standard shallow clause shape

```text
op(p, k) -> H
```

where `k` is the captured continuation without the handler reinstalled.  The
previous response-only syntax is retained as sugar for the fragment

```text
op(p) -> R
```

whose elaboration computes `R` and invokes `k` exactly once.

This choice is necessary for the promised derivation in Chapter IV:

```text
deep_Delta M with h
  := (fix loop. fun m ->
        shallow_Delta m with
          return x  -> h.return x
          op(p, k)  -> h.op(p, fun r -> loop (k r))) M
```

The recursive call is precisely handler reinstallation.  Deep handling is
therefore a derived program, not a new semantic primitive.

## The staged theorem program

At each extension boundary we separately test:

- type safety and deterministic decomposition;
- conservativity for old syntax;
- ordered effect soundness against runtime traces;
- preservation of graded/trace-indexed substitution and sequencing;
- lifting of base simulations, morphisms or logical relations;
- adequacy for the chosen base observations.

Chapter II and III are recursion-free, so proofs use finite evaluation and
well-founded trace trees.  Chapter IV replaces these with partiality/domain
structure, admissibility and fixed-point induction.  Claims about recursion
must not be silently imported from the finite chapters.

## Material no longer on the main line

Unordered rows, primitive deep handlers, and the previous two-chapter
finite-shallow/recursive-deep diagonal remain useful comparisons.  They are not
assumptions of the current theorem.  Quantitative occurrence bounds also remain
an optional later refinement of ordered trace languages.

