# Recursive Writer proof audit v2

## Status

**Independent obligation-by-obligation audit of the recursive Writer adequacy
argument.**  The purpose is to expose every use of continuity, admissibility,
determinism, and finite observation before generalizing.

## 1. Audited theorem chain

```text
domain equation
    |
    v
continuous term interpretation
    |
    +----> one-step soundness
    |
    v
projective logical relation
    |
    v
fundamental lemma
    |
    +----> return/request reflection
    |
    v
empty-row bottom/divergence adequacy
```

No arrow in this diagram uses normalization.

## 2. Domain-equation audit

The recursive functor is

$$
F_{A,\rho}(X)
=
\left(
W\times
\left(
D_A+
\sum_{\Delta,i}
D_{P_i}\times[D_{R_i}\to_c X]
\right)
\right)_\bot.
$$

### Positivity

The recursive variable occurs only as the codomain of
$[D_{R_i}\to_c X]$.  The response domain is fixed, so $F$ is covariant in $X$.
There is no negative recursive occurrence.

### Local continuity

Products, finite separated sums, lifting, and continuous-function codomain
formation preserve the directed colimits/bilimits used by the chosen domain
construction.  Writer multiplication is continuous because $W$ is a flat
countably based monoid and multiplication is a total function on its maximal
elements, extended strictly only where the lifted computation requires it.

### Size

The countability restriction is substantive.  It ensures that the displayed
sums and flat primitive domains remain in the chosen countably based category.
The general theorem should say “small relative to the selected domain
universe,” not silently quantify over class-sized signatures.

**Audit result:** no new obstruction for the chosen countable first theorem.

## 3. Continuity audit by syntax

| Construct | Continuous operation used |
|---|---|
| variable | projection |
| pair/injection | product/sum constructor |
| lambda | continuous currying |
| return | Writer-tree unit |
| application | evaluation |
| let | continuous bind |
| conditional/case | separated finite case analysis |
| `tell` | continuous Writer prefix constructor |
| free operation | request constructor |
| recursive function | parameterized least fixed point |
| handler | least fixed point of $\Phi_h$ |
| row weakening | constructor-preserving injection |

The recursive-function functional is continuous by the body induction
hypothesis.  The handler functional is continuous only if every clause
denotation is continuous in the resumption argument.  That follows from the
same syntax induction because resumptions are ordinary function values.

:::{prf:lemma} Syntactic continuity
:label: lem-recursive-writer-syntactic-continuity-v2

Every well-typed value and computation denotes a continuous map of its free
variables.  Every recursive-function body and handler clause induces a
continuous fixed-point functional.
:::

**Audit result:** proved by simultaneous typing induction; no separate
continuity assumption on language-defined clauses is needed.

## 4. Operational closure lemmas

The logical-relation proof implicitly uses the following.

:::{prf:lemma} Finite expansion closure
:label: lem-recursive-writer-expansion-v2

If $M\to^*N$ by internal/handled deterministic steps and

$$
N\mathcal C_A^\rho t,
$$

then

$$
M\mathcal C_A^\rho t.
$$
:::

:::{prf:proof}
Bottom is immediate.  For return/request, prepend the finite reduction to the
boundary evaluation witnessing the relation.  Determinism guarantees that it
does not expose a different boundary first.  Continuation obligations are
unchanged.
:::

:::{prf:lemma} Writer prefix closure
:label: lem-recursive-writer-prefix-relation-v2

If $M\mathcal C_A^\rho t$, then executing an already accumulated Writer prefix
$w$ relates the resulting configuration to $\mathsf{prefix}_w(t)$.
:::

This is checked separately at bottom, return, and request.

**Audit result:** these lemmas repair a previously implicit step in the beta,
recursive-unfolding, sequencing, and matching-handler cases.

## 5. Projective relation audit

Let $\pi_n$ expose at most $n$ request layers.  The finite relation
$\mathcal C_{A,n}$ is defined by induction on $n$:

- at depth zero, only bottom/no-information is required;
- return checks the value relation;
- request checks its root and invokes $\mathcal C_{A,n-1}$ pointwise on
  responses.

The full relation is

$$
\mathcal C_A=\bigcap_n\pi_n^{-1}(\mathcal C_{A,n}).
$$

### Infinite response sets

No compactness of the entire continuation function is assumed.  At each
projective depth the relation quantifies pointwise over all related response
values, but descends one request layer.  Thus infinite response arity affects
the size/accessibility assumption, not the logical depth measure.

### Admissibility

Each finite predicate contains bottom and is closed under directed suprema.
Preimage under continuous $\pi_n$ preserves this property, and arbitrary
intersection preserves it as well.

**Audit result:** the coinductive continuation clause is well-defined through
finite projections.  The proof does not rely on the false statement that every
well-founded or infinite-arity request tree is compact.

## 6. Recursive-function audit

For $R=\mathsf{rec}\ f(x).M$, the approximation proof needs:

1. constant-bottom function relates to $R$;
2. relatedness to $f_n$ allows the body fundamental lemma with $R/f$;
3. one operational unfolding is removed using finite expansion closure;
4. admissibility passes to $\bigsqcup_n f_n$.

All four obligations are now explicit.  The proof uses no syntactic finite
unrolling transformation and allows the body to call $f$ in higher-order
positions permitted by its type.

**Audit result:** closed under the chosen effectful recursive-function syntax.

## 7. Handler fixed-point audit

For a candidate semantic handler $g$, let $\mathcal P(g)$ state operational/
semantic relatedness after handling.

### Bottom

$\mathcal P(\bot)$ holds because computation bottom imposes no boundary
obligation.

### Functional closure

$\mathcal P(g)\Rightarrow\mathcal P(\Phi_hg)$ uses exactly four cases:

- source bottom;
- return and related return clause;
- matching request and related clause/resumption;
- residual request with the pending handler retained pointwise.

Finite expansion closure accounts for the operational handler step in the
matching and return cases.

### Admissibility of $\mathcal P$

For a directed chain $g_j$, evaluation at any fixed tree $t$ is continuous:

$$
(\bigsqcup_jg_j)(t)=\bigsqcup_jg_j(t).
$$

Computation-relation admissibility therefore closes $\mathcal P$ under the
chain.  Universal quantification over source terms and related inputs is an
intersection of admissible predicates.

**Audit result:** fixed-point induction is justified for Writer, including
language-defined multi-shot clauses.  Resource validity remains a separate
base-interaction question.

## 8. Adequacy audit

### Forward direction

Finite operational evaluation plus one-step soundness gives the exact semantic
root.  Constructor separation preserves Writer log and nominal operation.

### Reverse direction

The closed fundamental lemma unfolds the return/request clause of
$\mathcal C$.  No compactness or normalization argument is additionally needed.

### Bottom

At empty row, nonbottom has only a return constructor.  Return reflection and
deterministic decomposition imply bottom iff there is infinite boundary-free
reduction.

The final inference is classically phrased.  A constructive version should use
finite nontermination approximants rather than the proposition “evaluation is
infinite.”

**Audit result:** the stated termination-sensitive adequacy follows.

## 9. Audit verdict

The paper proof is internally coherent under:

1. the selected countably based bifinite-domain construction;
2. deterministic typed Writer operational semantics;
3. first-order nominal signatures small in that category;
4. the fixed effectful recursive-function syntax;
5. ordinary classical reasoning for the final divergence equivalence.

No remaining step assumes normalization or a black-box PCF adequacy theorem.
The remaining risk is proof-engineering detail in the bilimit and simultaneous
logical-relation construction, suitable for mechanization or independent
formal audit.
