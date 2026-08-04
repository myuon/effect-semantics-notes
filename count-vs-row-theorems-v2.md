# Count versus row theorems v2

## Status

**Comparison after completing the unordered theorem first.**

## 1. Unchanged theorems

Adding optional counts does not change the statements or proofs of:

- old-language operational conservativity;
- canonical base denotation embedding;
- direct deep-handler semantics;
- matching/nonmatching scope;
- one-step soundness;
- morphism lifting;
- logical-relation lifting;
- adequacy assumptions;
- noncommutation with old handlers such as `try`.

These results depend on operation structure and handler scope, not on how
precisely new effects are annotated.

## 2. Strengthened theorems

| Question | Unordered row | Quantitative row |
|---|---|---|
| can $\Delta$ escape? | yes/no | remaining upper count |
| conditional request | label present | count $\leq1$ |
| sequential requests | label present | counts add |
| handler clause invocations | unknown | $\leq n$ for affine handler |
| handler output new effects | support union | $(\nu\setminus\Delta)+n\kappa+\tau$ |
| multi-shot amplification | invisible | expressible after adding usage bound |

The central strengthened statement is

$$
\Delta^{\le n}
\xrightarrow{H_\Delta}
\Delta^{\le0}
$$

for $\Delta$-free exhaustive affine clauses, together with a bound on other
effects introduced by at most $n$ clause invocations.

## 3. Theorems still unavailable

Counts alone do not determine:

- the insertion order of clause effects in a noncommutative Writer grade;
- whether two clause effects commute with intervening base behavior;
- whether state is global, restored, or branched across resumptions;
- whether a clause-generated exception lies inside an old `try`;
- whether duplicating a continuation is valid for a linear resource;
- exact occurrence on every path.

Therefore the Writer/State/Exception boundary examples remain valid after
adding counts.  They become better diagnosed, not automatically solved.

## 4. Effect on the main theorem

The unordered main theorem remains the default:

> Under `BaseSafety` and optional resumption/observation hypotheses, unordered
> free operations and exhaustive deep handlers preserve safety,
> conservativity, compositional semantics, morphisms, relations, and adequacy.

The quantitative theorem is an optional corollary/refinement:

> If the new-effect abstraction additionally tracks per-path occurrence upper
> bounds and resumptions are affine, the extension also preserves quantitative
> sequencing and gives a sound numeric handler transformer.

Thus count does not add a new runtime language feature.  It strengthens static
information and handler effect calculation.

## 5. Effect on assumptions

The unordered theorem needs no continuation usage discipline for free-row
discharge.  Even a multi-shot deep handler can ensure that no $\Delta$ escapes
if every duplicated continuation remains under the handler.

The simple quantitative transformer does need affinity.  Without it, one
source request can cause a suffix containing many more requests to be executed
multiple times.

Hence the assumption change is:

$$
\text{unordered discharge}
\quad\text{requires no usage bound},
$$

$$
\text{linear count formula}
\quad\text{requires resumption usage}\leq1.
$$

For multi-shot counts, a usage grade $m$ and a nonlinear/geometric transformer
are required.

## 6. Relationship to old base grades

If a base effect abstraction supplies a sound repetition/insertion operator

$$
\mathsf{insert}^{\le n}_E(b,e),
$$

then the count theorem can parameterize a stronger combined result:

$$
(b,\nu)
\xrightarrow{H_\Delta^e}
\left(
\mathsf{insert}^{\le\nu(\Delta)}_E(b,e),
\Phi^{\mathrm{aff}}(\nu)
\right).
$$

But $\mathsf{insert}^{\le n}_E$ is additional base/handler interaction
structure.  It is not derivable from a monoid multiplication alone when $E$ is
noncommutative.

Examples:

- an unordered idempotent base may use $b\sqcup e$;
- a commutative quantitative base may use
  $b\cdot(1\sqcup e\sqcup\cdots\sqcup e^n)$;
- an ordered Writer base needs a shuffle/insertion language or a coarser top;
- Exception needs scope information in addition to repetition count.

## 7. Recommended final architecture

The current evidence supports:

```text
Layer 0: BaseSafety / BaseResumptionModel
    |
Layer 1: unordered free rows + deep discharge       (default theorem)
    |
Layer 2: optional occurrence-count refinement       (affine theorem)
    |
Layer 3: optional base interaction / ordered scope   (instance-specific)
```

This ordering keeps the broadly applicable result independent of quantitative
typing while making count available exactly where it adds information.

## 8. Open quantitative obligation

The affine theorem is ready at paper level.  The next quantitative task, if
chosen, is not to revisit unordered safety.  It is to formalize a resumption
usage judgment and prove or correct the geometric multi-shot transformer
{prf:ref}`conj-multishot-count-handler-v2`.
