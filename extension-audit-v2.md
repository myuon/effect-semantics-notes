# Extension audit v2

## Purpose

This is the main experiment ledger for the revised program.  Each candidate extension must state its input assumptions and fill this table with a proof, a cited theorem, a counterexample, or `open`.

## Property matrix

| Property | Trivial base | General base, base-pure clauses | General base, base-effectful clauses |
|---|---:|---:|---:|
| typing embedding | expected | expected | expected |
| operational conservativity | expected | expected | expected |
| denotational embedding | standard free construction | paper proof under resumption-existence hypothesis | paper proof under resumption-existence hypothesis |
| preservation | standard | paper proof for the free row | free-row preservation proved; precise base grade interaction-dependent |
| no unhandled operation at empty row | standard | expected | expected |
| deep elimination of $\Delta$ from free row | standard | expected | expected if clauses do not re-emit $\Delta$ |
| adequacy preservation | standard recursion-free case | termination-conditional paper proof | termination-conditional paper proof |
| morphism lifting | structural | paper proof | paper proof for compatible clauses |
| logical-relation lifting | structural | paper proof | paper proof for compatible clauses |
| precise output base grade | trivial | same $e$ | generally unavailable from an unordered row |
| multi-shot safety | trivial pure base | needs audit | needs duplicability/discardability audit |

“Expected” is not a proved status.  Results migrate to the claims ledger only after proof.

The generic unordered results and their exact assumptions are collected in
[Generic resumption extension v2](generic-resumption-extension-v2.md) and
[Unordered preservation summary v2](unordered-preservation-summary-v2.md).
Occurrence counts are an optional refinement, not an assumption of those
results; see [Quantitative row extension v2](quantitative-row-extension-v2.md)
and [Count versus row theorems v2](count-vs-row-theorems-v2.md).

## Concrete-instance progress

| Instance | Syntax/examples | Operational decomposition | Preservation | Empty-row safety | Deep elimination | Denotational correspondence |
|---|---:|---:|---:|---:|---:|---:|
| Pure | fixed | inherited as Writer without `tell` | paper proof | paper proof | paper proof | open |
| Writer | complete | paper proof | paper proof | paper proof | paper proof | paper proof, termination-conditional adequacy |
| State | complete | paper proof | paper proof | paper proof | paper proof | paper proof, termination-conditional adequacy |
| Exception | complete, including old `try` | paper proof with raise outcome | paper proof | paper proof for new row | paper proof | paper proof, termination-conditional adequacy |

“Paper proof” means a proof argument is written in these notes but is not yet
machine checked.  The Writer arguments are in [Writer operational metatheory
v2](writer-operational-metatheory-v2.md).

State results are in [State deep-handler study
v2](state-deep-handler-study-v2.md) and [State free-tree semantics
v2](state-free-tree-semantics-v2.md).  Exception results are in [Exception
handler interaction v2](exception-handler-interaction-v2.md) and [Exception
free-tree semantics v2](exception-free-tree-semantics-v2.md).  The extracted
common boundary is [Concrete base comparison
v2](concrete-base-comparison-v2.md).

## First boundary example: effectful clauses

Suppose the input has base grade $b$ and free row $\{\Delta\}$.  Let the $\Delta$-clause perform base effect $k$ before resuming.

The same static input annotation permits executions with zero, one, or several $\Delta$ requests.  Deep handling may therefore produce base behavior resembling

$$
b,
\qquad
k\otimes b,
\qquad
k\otimes b_1\otimes k\otimes b_2,
\qquad\ldots
$$

where the original base behavior itself may be split around operation sites.  If $E$ is noncommutative, neither the number nor the insertion positions of $k$ are determined by $(b,\{\Delta\})$.

:::{prf:conjecture} Unordered-row precision boundary
:label: conj-unordered-boundary

There is no uniform principal-grade transformer for arbitrary noncommutative base effect monoids that computes the precise base grade of an effectful deep handler from only an input base grade $b$, an unordered may-row $\rho$, and a clause grade $k$.
:::

A formal counterexample should use two computations with the same input grade but different placements or counts of $\Delta$, whose handled base traces have no common principal grade below the proposed result.

## Candidate remedies to compare

1. **Base-pure clause restriction:** $k=1$.
2. **Coarse top:** weaken the result to $\top$; safe but usually uninformative.
3. **Commutative idempotent base:** repeated insertion collapses to $b\sqcup k$.
4. **Iteration:** use $k^*$, still requiring a law for insertion relative to $b$.
5. **Occurrence counts:** retain an upper bound for each handled interface.
6. **Ordered trace refinement:** calculate insertion pathwise, then abstract back to the public row system.

The remedies should be ordered by required structure and precision, rather than selecting one prematurely.

## Handler fragments to test

For each fragment, repeat the audit.

1. operation generation and forwarding only;
2. affine one-shot catch: continuation used zero or one time;
3. linear deep handler: every matching request resumes exactly once;
4. unrestricted deep handler: continuation used zero or many times;
5. scoped/higher-order handler.

This distinction is essential for IO, resources, cancellation, concurrency, and other base mechanisms where duplicating a continuation is observably different or invalid.

## Immediate proof obligations

- Fix a precise baseline calculus and row algebra.
- State handler operational rules, including forwarding and reinstallation.
- Prove row weakening, substitution, preservation, and effect-aware progress.
- Define the free tree semantics and deep fold.
- Prove operational/denotational handler commutation.
- Formulate base embedding independently from handler clauses.
- Produce the first base-effectful counterexample before attempting the maximal theorem.
