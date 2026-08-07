# Chapter IV — recursion certificate and derived-deep theorem

## Status

**Conditional paper theorem.**  This page records exactly what must be added
to `ShallowCert` and what is then preserved.

## 1. Recursive input certificate

`RecBaseCert` extends `ShallowCert` with:

1. typed CBV unfolding and preservation for recursive calls;
2. a pointed/order-enriched model with a selected continuous iteration;
3. agreement of source unfolding with that iteration;
4. an admissible computation relation closed under approximation;
5. recursive resumption solutions and continuous shallow constructors;
6. a declared observation level for divergence or productive infinity;
7. an iteration-closed ordered effect operation when recursive effects are
   to receive a finite annotation.

Items 2–5 are genuine additional hypotheses.  They cannot be reconstructed
from the finite `ShallowCert` or from monad laws.

## 2. Recursive safety

:::{prf:theorem} Recursive preservation and progress
:label: thm-recursive-preservation-v5

Under `RecBaseCert`, recursive unfolding preserves value types and ordered
may-effect bounds.  A closed well-typed computation either is a classified
boundary or has a unique next step.  Consequently, a maximal run reaches a
classified boundary or is infinite.
:::

The final alternative is new: normalization from the recursion-free chapters
does not survive.

## 3. Derived/deep coincidence

:::{prf:theorem} Derived source handler equals semantic deep handler
:label: thm-derived-deep-coincidence-v5

The denotation of the fixpoint-and-shallow source expansion equals
$\operatorname{lfp}(\mathcal D_h)$.
:::

**Proof.**  Unfolding the source `loop` once gives exactly the Chapter-III
shallow map whose matching continuations are wrapped by the previous
approximation; nonmatching continuations remain under that shallow map.  Hence
the $n$th source approximant denotes
$\mathcal D_h^n(\bot)$.  Continuity and the source-fixpoint agreement field
identify their suprema. $\square$

## 4. Deep elimination

:::{prf:theorem} Elimination of an exhaustive interface
:label: thm-deep-elimination-v5

If $h$ is exhaustive for $\Delta$, all clause results are outwardly
$\Delta$-free, matching continuations are recursively wrapped, and transparent
forwarding retains the pending handler, no finite execution prefix exposes an
unhandled $\Delta$ request.
:::

**Proof sketch.**  Induct on finite unfoldings and finite reductions.  A
matching request enters a clause; a nonmatching request is rebuilt with the
invariant in its continuation.  Admissibility closes the semantic statement
at the least fixed point.  Divergence does not invalidate the prefix safety
invariant.

## 5. Adequacy

:::{prf:theorem} Recursive adequacy transport
:label: thm-recursive-adequacy-v5

If the Chapter-III logical relation is admissible and compatible with selected
iteration, the fundamental lemma extends to recursion and the derived deep
handler.  Thus finite return, old-outcome, and escaping-request adequacy are
preserved.  Divergence and productive-infinite adequacy are obtained only at
the observation level explicitly supplied by `RecBaseCert`.
:::

The recursion case uses fixed-point induction.  The handler case uses the
derived/deep coincidence theorem rather than assuming a primitive deep
operator.

## 6. Ordered-effect theorem

For each finite unfolding, Chapter III transforms occurrences in their
original order, taking the prefix before each first match to be $\Delta$-free.
For unbounded recursion, suppose $e^*$ safely closes finite
iteration and $\Phi_h$ is continuous/closure-compatible.  Then the transformed
recursive bound is safely covered by the corresponding closed output, for
example

$$
(b\cdot\Delta\cdot e)^*
\longmapsto
(b\cdot e'\cdot e)^*.
$$

This is an inequality-level may-effect result.  Exact equality, multiplicity,
or a least principal word is outside the basic theorem.

## 7. Chapter-IV structure-preservation theorem

:::{prf:theorem} Recursive derived-deep certificate
:label: thm-recursive-derived-deep-certificate-v5

`RecBaseCert`, an exhaustive handler certificate, and a closure-compatible
effect transformer yield `DeepCert`, containing:

- recursive type safety and old-program conservativity;
- the definability of deep handling from fixpoint plus shallow handling;
- operational and denotational deep equations;
- elimination of the handled interface from every finite outer observation;
- preservation of finite adequacy;
- conditional divergence/productive-trace adequacy;
- ordered effect transformation under iteration closure.
:::

## 8. Sharp limits

The fixed-point induction, elimination invariant and recursive logical-relation
argument are expanded in
[Chapter IV — detailed recursive and derived-deep proofs](chapter-4-proof-details-v5.md).

The theorem does not provide termination, exact effect counts, unrestricted
multi-shot resource safety, commutation with old handlers, full abstraction,
or productive traces in a bottom-only model.  These require separate
certificates rather than stronger prose around “an arbitrary base effect.”
