# Recursive base adequacy package v2

## Status

**Generic interface extracted from the recursive Writer proof.**  This is the
recursion-aware replacement for the termination premise in the unordered main
theorem.

## 1. Purpose

The recursion-free theorem used:

> if evaluation reaches a classified boundary, denotation and operation agree.

With recursion, a generic extension theorem must additionally explain semantic
bottom/infinite approximation and operational reflection.  It should not force
every base language to use Writer's particular CPO.

## 2. `RecursiveBaseAdequacy`

A recursive base instance supplies the following fields.

### RA-1: recursive operational safety

- typed deterministic decomposition;
- preservation;
- a typed recursive unfolding rule;
- classified base outcomes;
- finite expansion closure of boundary evaluation.

### RA-2: enriched computation model

A pointed, order-enriched computation semantics with:

- continuous return and bind;
- directed suprema;
- parameterized least fixed points or complete Elgot iteration;
- continuous interpretations of base primitives.

### RA-3: recursive free resumption

For each row $\rho$, a carrier

$$
\mathsf{CRes}_{T,\rho}A
$$

exposing approximation-sensitive return, base outcome, and nominal free-request
boundaries, with continuous row weakening and bind.  It also supplies a
continuous iteration-preserving embedding of the recursive base computation
model as the empty-free-row fragment.

### RA-4: finite observations

A separating family of continuous finite projections

$$
\pi_n:\mathsf{CRes}_{T,\rho}A\to R_{\rho,n}A
$$

such that equality/observation is determined by all projections.  An explicit
`Tau`/guarded model may provide step indices instead of domain projections.

### RA-5: primitive boundary correctness

Every base primitive relates its operational boundary action to its semantic
operation.  This is instance-specific: Writer checks log prefix, State checks
state transition, and Exception checks raised outcome.

### RA-6: admissible logical relation

Typed value and computation relations:

- contain bottom/no-information;
- are closed under directed suprema or guarded later steps;
- reflect finite return, base outcome, and free-request observations;
- are stable under substitution, bind, and row weakening.

### RA-7: recursive handler compatibility

The handler functional is continuous/guarded and preserves the logical
relation when its return and operation clauses do.  Its selected least/guarded
fixed point gives the semantic deep handler.

### RA-8: observation policy

The package declares which of the following it reflects:

1. finite boundaries only;
2. bottom versus boundary divergence;
3. productive infinite observable traces.

The theorem must not infer Level 3 from a Level 2 model.

## 3. Generic fundamental lemma

:::{prf:theorem} Recursive extension fundamental theorem
:label: thm-recursive-base-fundamental-v2

Assume `BaseSafety` and RA-1--RA-7.  If source and semantic environments are
related, every well-typed value/computation in the unordered free-operation and
deep-handler extension is related to its denotation.
:::

:::{prf:proof}
Induct simultaneously on typing.  Old cases are provided by the base package;
return, application, sequencing, branching, and free requests use relation
compatibility.  Recursive functions use admissible fixed-point induction.
Deep handlers use admissibility/guardedness of the handler predicate and RA-7.
Subeffecting uses row-relation monotonicity.
:::

This theorem is parametric in the base boundary relation; it does not inspect a
Writer log or State cell directly.

## 4. Generic adequacy theorem

:::{prf:theorem} Recursive unordered adequacy preservation
:label: thm-recursive-unordered-adequacy-v2

Under `RecursiveBaseAdequacy`, adding unordered first-order free operations and
exhaustive deep handlers preserves:

- one-step soundness;
- finite return/base-outcome/request adequacy;
- deep discharge at every finite observation;
- old recursive-language denotational conservativity;
- bottom/divergence adequacy when RA-8 includes Level 2;
- productive infinite-trace adequacy only when RA-8 includes Level 3.
:::

The proof combines the generic fundamental theorem with operational
determinism/decomposition and the chosen observation policy.

## 5. Morphisms and relations

The recursion-free morphism theorem quantified over monad morphisms.  The
recursive version requires

$$
q(f^\dagger)=(qf)^\dagger
$$

or the corresponding preservation of guarded limits/projections.

:::{prf:theorem} Recursive morphism lifting
:label: thm-recursive-morphism-lifting-v2

An iteration-preserving base monad morphism that preserves finite observations
and primitives lifts through recursive resumptions and compatible deep
handlers.
:::

Likewise, arbitrary structural relations are replaced by admissible or guarded
relations.  This is a strengthening of hypotheses, not a failure of the free
extension.

## 6. Instance table

| Instance | RA-2 model | Level 2 | Level 3 |
|---|---|---:|---:|
| Pure | lifting/partiality | expected standard | silent behavior only |
| Writer | recursive partial Writer domain | proved on paper | no |
| State | partial global State domain | proved on paper | transient trace not retained |
| Exception | lifted return/raise domain | proved on paper | not relevant without visible steps |

## 7. Answer to the preservation question

General recursion does not invalidate the unordered extension theorem.  It
changes the certificate required from the base:

```text
normalization or termination premise
            becomes
admissible/guarded recursive adequacy package.
```

Operational row safety and deep discharge need none of RA-2--RA-8.  Denotational
soundness and adequacy need progressively more of the package.  This preserves
the layered structure of the research result.

## 8. Next discriminating instance

State validates the package with an initial-state-indexed logical relation and
global sequential multi-shot resumptions.  Exception validates it with a
separate abortive outcome and preserves the noncommuting scope of old `try` and
new handlers.  See [Recursive State adequacy
v2](recursive-state-adequacy-v2.md) and [Recursive Exception adequacy
v2](recursive-exception-adequacy-v2.md).  The next genuinely stronger test is a
Level-3 base observation that retains productive infinite traces.
