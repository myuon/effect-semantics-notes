# Recursive Exception adequacy v2

## Status

**Paper-level validation of `RecursiveBaseAdequacy` with abortive outcomes and
old-handler scope.**

## 1. Four-way computation relation

Reuse the typed value relation.  Relate a closed computation $M$ to
$t\in\mathsf{CXTree}_\rho A$ by:

- $t=\bot$: no finite-boundary obligation;
- $t=\mathsf{ret}(d)$: operational evaluation returns a related value;
- $t=\mathsf{raise}(e)$: operational evaluation exposes the same base
  exception;
- $t=\mathsf{req}(\Delta,i,p,k)$: operational evaluation exposes the same
  nominal request, with related parameter and pointwise related continuation.

Construct the relation through finite bilimit projections.  The new raise case
is a separated finite constructor and preserves admissibility.

## 2. Fundamental lemma

:::{prf:theorem} Recursive Exception fundamental lemma
:label: thm-recursive-exception-fundamental-v2

Every well-typed recursive Exception/free-handler term is related to its
$\mathsf{CXTree}$ denotation.
:::

:::{prf:proof}
Reuse the generic value, sequencing, recursion, free-request, and deep-handler
cases.

- `raise(e)` immediately has the semantic raise constructor.
- sequencing propagates a raise without invoking its continuation.
- `try M with h_E` uses the return/raise/request/bottom cases of
  $\mathsf{Try}_{h_E}$; a request continuation retains the operational `try`.
- the new deep handler propagates an already exposed base raise and handles
  free requests by its least-fixed-point induction.

Clause relatedness follows from the typing induction hypotheses.
:::

## 3. Finite-boundary adequacy

:::{prf:theorem} Recursive Exception finite adequacy
:label: thm-recursive-exception-finite-adequacy-v2

For every closed first-order computation, denotational return, base raise, and
free-request roots are equivalent to their operational finite-boundary
observations, with related values/parameters/continuations.
:::

Forward follows from one-step soundness.  Reverse unfolds the closed
fundamental relation.

## 4. Divergence adequacy

At empty free row,

$$
\mathsf{CXTree}_\varnothing A\cong(A+E)_\bot.
$$

:::{prf:theorem} Recursive Exception bottom adequacy
:label: thm-recursive-exception-bottom-adequacy-v2

For a closed ground computation with empty outward free row,

$$
\llbracket M\rrbracket=\bot
$$

iff deterministic execution reaches neither return nor base raise and takes
infinitely many steps.
:::

Empty-row safety excludes a new free request.  The fundamental lemma reflects
both possible nonbottom boundaries.

## 5. Scope adequacy

:::{prf:theorem} Recursive Exception/handler scope adequacy
:label: thm-recursive-exception-scope-adequacy-v2

The semantic compositions

$$
\mathsf{Try}_{h_E}\circ H_{\Delta,h}
$$

and

$$
H_{\Delta,h}\circ\mathsf{Try}_{h_E}
$$

agree with the corresponding operational nestings on return, raise, residual
request, and divergence observations.
:::

In particular, the known noncommutation counterexample with a clause-generated
raise remains valid under recursion.  Divergence adds a fourth shared strict
case but does not repair the scope difference.

## 6. Package validation

| Field | Exception realization |
|---|---|
| RA-1 | deterministic return/step/raise/request decomposition |
| RA-2 | lifted partial Exception domain |
| RA-3 | $\mathsf{CXTree}$ recursive resumption |
| RA-4 | bilimit finite projections |
| RA-5 | exact `raise` and `try` boundary behavior |
| RA-6 | four-way admissible relation |
| RA-7 | strict continuous `try` and free-handler functionals |
| RA-8 | Level 2: return/raise/request/divergence |

Thus `RecursiveBaseAdequacy` covers a base with an abortive outcome without
changing its generic fields.

## 7. Three-instance conclusion

Writer, State, and Exception now share:

- pointed/iterative recursive computation semantics;
- projective finite observations;
- admissible typed logical relations;
- least-fixed-point deep handlers;
- finite-boundary and divergence adequacy.

They differ only in their base boundary algebra and handler interaction laws.
This is strong evidence for the layered generic theorem, while still not
claiming that an arbitrary opaque monad automatically has this structure.
