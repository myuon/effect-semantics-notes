# Research question and staged development

## Status

**Current research spine.**  This page supersedes the two-chapter diagonal of
v4.  The development now adds one construct at a time:

1. a fixed base language and ordered upper-bound effects;
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
| II | free operation interfaces and ordered effect extension | is the extension conservative and compositional? |
| III | shallow handlers | how does one exposed operation transform an effect bound? |
| IV | fixed points and derived deep handlers | which finite results survive recursion, and when does recursive reinstallation discharge an interface? |

The chapters are cumulative.  In particular, Chapter IV does not introduce a
second primitive handler calculus.

## Ordered upper-bound effects

Let the base effect algebra be a preordered monoid

$$
(B,\cdot,1,\leq).
$$

An annotation $b$ is a static upper approximation of effects that a computation
may perform.  It need not equal what one particular execution performs.
Sequencing uses the noncommutative product, while branching chooses any common
upper bound using $\leq$.  In particular, $1\leq b$ permits a pure branch to be
typed at $b$.  The type system retains order without predicting the unique
runtime path.

After adding interfaces $\Delta\in\mathcal D$, effect bounds are reduced words in the
free product

$$
\widehat E = B * \mathcal D^*.
$$

We use

$$
b\cdot\Delta\cdot e
$$

as an ordered upper bound.  It says that a possible execution reaches the
$\Delta$ request only after effects bounded by $b$, and its continuation is
bounded by $e$.  It does not say that every execution performs every factor.

## Guiding shallow equation

For the affine response fragment, suppose $b$ is $\Delta$-free and a $\Delta$
clause has effect bound $e'$ and supplies exactly one response to the captured
tail.  The intended effect transformation is

$$
b\cdot\Delta\cdot e
\longmapsto
b\cdot e'\cdot e.
\tag{Effect-Shallow}
$$

On a matching execution the prefix $b$ has already happened, the exposed
request is replaced by the clause computation, and the continuation retains
$e$.  The equation computes a sound output bound; it is not an equality with a
runtime record.

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

A request from $\Gamma\neq\Delta$ is transparently forwarded with the shallow
handler retained in its continuation. In the optional partial extension, an
operation $i\notin J$ from the same interface is forwarded in the same way.
Thus shallow handling searches across unhandled requests but stops reinstalling
itself after the first selected clause. Interface-level elimination remains
the exhaustive case $J=I_\Delta$. Deep handling differs by wrapping the
selected matching continuation.

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

The main recursion-free answer is now stated first as the
[Functorial free-effect extension and adequacy transport
theorem](functorial-extension-theorem-v5.md).  It reorganizes the original
research equations into the following dependency chain:

$$
\begin{array}{c}
T\mapsto\mathsf F_\Delta T
\\[1mm]\Downarrow\\[-1mm]
q\mapsto\mathsf F_\Delta q,\quad
R\mapsto\mathsf{Str}_\Delta R
\\[1mm]\Downarrow\\[-1mm]
\mathsf{Str}_\Delta(\operatorname{Graph}q)
=\operatorname{Graph}(\mathsf F_\Delta q)
\\[1mm]\Downarrow\\[-1mm]
\mathsf{Str}_\Delta(V^{\top\top})
\subseteq V^{\top_\Delta\top_\Delta}
\\[1mm]\Downarrow\\[-1mm]
\text{TT-compatible shallow handling and adequacy transport.}
\end{array}
$$

Chapters I--III supply the definitions and detailed proofs behind this result.
The [graded TT-lifting page](graded-tt-lifting-v5.md) separates structural
generation from observational closure.
Chapter IV is deliberately a second theorem: recursion invalidates finite
normalization and requires domain-theoretic structure that is not part of the
free-extension functor itself.

The source of this functor is the category of graded monads for which the
required [strong graded FreeT](graded-freet-existence-v1.md) exists. This is a
substantive restriction. Accessibility discharges carrier existence in
standard Set-based examples; a concrete graded construction must additionally
supply bind, strength, weakening and the coherent base action. Ordinary
ungraded FreeT derives that action from fold/unfold and base multiplication.

This restriction begins only at semantic composition. The
[assumption dependency audit](assumption-dependency-audit-v5.md) shows that
operation syntax, type safety, request decomposition and old operational
conservativity do not depend on FreeT existence. The FreeT premise first
enters when interpreting the extended language compositionally.

At each extension boundary we separately test:

- type safety and unique evaluation-position decomposition;
- conservativity for old syntax;
- ordered effect safety under runtime reduction;
- preservation of graded substitution and sequencing;
- lifting of base simulations, morphisms or logical relations;
- adequacy for the chosen base observations.

Chapter II and III are recursion-free, so proofs use finite evaluation and
well-founded operation trees.  Chapter IV replaces these with partiality/domain
structure, admissibility and fixed-point induction.  Claims about recursion
must not be silently imported from the finite chapters.

The detailed development follows the [common chapter
method](chapter-method-v5.md).  Each chapter runs syntax, operational
semantics, concrete Writer/State/Exception calculations, denotation, local
proofs and package extraction in that order.  Chapter $n+1$ receives only
the explicit package exported by Chapter $n$.

The package names abbreviate formally declared conditions, not unspecified
bundles of “good properties.”  The cumulative theorem is read in three stages.

1. A split `BasePackage` containing operational $S$, denotational $T$, and their
   comparison, together with the strong graded FreeT objects
   $\widehat S=\operatorname{FreeT}_\Sigma(S)$ and
   $\widehat T=\operatorname{FreeT}_\Sigma(T)$, yields `FreeExtensionPackage` and the
   lifted $\widehat T\to\widehat S$ comparison. Finite/separated observations
   are needed only for a subsequent TT reflection theorem.
2. `FreeExtensionPackage`, a closed graded TT pole and either `AffineHandlerLaws` or
   `HandlerPackage` yield `ShallowHandlerPackage`.
3. `ShallowHandlerPackage` and the appropriate *component* of `RecBasePackage` yield the
   corresponding recursive conclusion: recursive safety, least-fixed-point
   definability, recursive relation preservation, adequacy at the declared
   observation level, or effect closure.  These conclusions form the
   non-eliminating `DeepHandlerPackage`.  Exhaustiveness and outwardly $\Delta$-free
   clauses are additional premises only for `DeepElimination`.

In symbols, the conclusions are

$$
\mathsf{FreeExtensionPackage},\qquad
\mathsf{ShallowHandlerPackage},\qquad
\mathsf{DeepHandlerPackage}
\quad\text{and, under the stronger elimination premises,}\quad
\mathsf{DeepElimination},
$$

but each is justified only by the numbered premises on its package page.

Each conjunct, its quantified type, and its equations are written out in the
package section of the corresponding chapter.  This cumulative display is
an assembly theorem; the functorial theorem above is the sharper answer to the
original object/morphism/relation-lifting question.

## Material no longer on the main line

Unordered rows, trace-language refinements, primitive deep handlers, and the previous two-chapter
finite-shallow/recursive-deep diagonal remain useful comparisons.  They are not
assumptions of the current theorem.  Quantitative occurrence bounds also remain
an optional later refinement of the ordered effect algebra.
