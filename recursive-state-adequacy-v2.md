# Recursive State adequacy v2

## Status

**Paper-level validation of `RecursiveBaseAdequacy` for partial global State.**

## 1. State-indexed logical relation

Reuse the value relation $\mathcal V_A$.  For a closed computation $M$ and
$t\in\mathsf{CSTree}_\rho A$, define

$$
M\mathrel{\mathcal C_{A,S}^\rho}t
$$

when, for every related/identical initial state $s$, the operational
configuration $\langle s,M\rangle$ agrees with $t(s)$:

- $t(s)=\bot$ imposes no finite-boundary obligation;
- $t(s)=\mathsf{ret}(d,s')$ requires
  $\langle s,M\rangle\Downarrow\mathsf{ret}(V,s')$ with
  $V\mathcal V_A d$;
- a request root requires the same nominal operation, parameter, and request-
  time state, with pointwise related response continuations.

The relation is constructed through finite bilimit projections exactly as in
Writer, with an additional outer universal quantification over $s$.

## 2. Admissibility

:::{prf:lemma} State-indexed admissibility
:label: lem-recursive-state-admissibility-v2

For each closed $M$, the set

$$
\{t\mid M\mathcal C_{A,S}^\rho t\}
$$

contains the constant-bottom transformer and is closed under directed suprema.
:::

:::{prf:proof}
Function-space suprema are pointwise.  At each fixed $s$, apply the finite-
projection Writer-style argument with state replacing Writer prefix.  Universal
quantification over states is an intersection of admissible predicates.
:::

## 3. Fundamental lemma

:::{prf:theorem} Recursive State fundamental lemma
:label: thm-recursive-state-fundamental-v2

Every well-typed recursive State/free-handler term is related to its
$\mathsf{CSTree}$ denotation under related closing environments.
:::

:::{prf:proof}
The pure, free-operation, recursive-function, and handler cases reuse the
generic proof.

- `get` returns the operational current state and leaves it unchanged, matching
  its semantic map.
- `put(s')` returns unit with state $s'$, again exactly matching.
- sequencing applies the continuation at the state returned by the first
  computation.
- a matching handler clause begins at the state stored in the request boundary;
  applications of the related resumption are themselves State computations and
  therefore consume the current clause state at each invocation.

Admissible fixed-point induction handles recursive functions and handlers.
:::

## 4. Finite-boundary adequacy

:::{prf:theorem} Recursive State finite adequacy
:label: thm-recursive-state-finite-adequacy-v2

For every closed first-order $M$ and initial state $s$:

$$
\langle s,M\rangle\Downarrow\mathsf{ret}(V,s')
$$

iff

$$
\llbracket M\rrbracket(s)=\mathsf{ret}(d,s')
$$

for related $V,d$.  The analogous equivalence holds for a finite unhandled
free request, including equality of its request-time state.
:::

Forward uses one-step soundness; reverse uses the closed fundamental lemma.

## 5. Divergence adequacy

:::{prf:theorem} Recursive State bottom adequacy
:label: thm-recursive-state-bottom-adequacy-v2

For a closed ground computation with empty outward row and every initial state
$s$:

$$
\llbracket M\rrbracket(s)=\bot
$$

iff the deterministic execution from $s$ reaches no return boundary and takes
infinitely many steps.
:::

Empty-row safety excludes free requests.  Nonbottom at empty row is a return
with a final state and is reflected by the fundamental lemma.

This theorem does not recover the sequence of states traversed by a divergent
execution.

## 6. Handler adequacy and global-state choice

:::{prf:theorem} Recursive State handler adequacy
:label: thm-recursive-state-handler-adequacy-v2

The direct operational deep handler agrees with the least-fixed-point State
handler on finite boundaries and, at empty target row, on bottom/divergence for
every initial state.
:::

The matching case verifies the important interaction law:

> clause execution starts in the request-time state, while each resumption use
> starts in the state current at that invocation.

Thus adequacy validates the intended global sequential interpretation rather
than silently selecting state rollback or branch-local copies.

## 7. Package validation

State instantiates the generic fields as follows.

| Field | State realization |
|---|---|
| RA-1 | deterministic state machine plus recursive unfolding |
| RA-2 | partial continuous State transformer |
| RA-3 | $\mathsf{CSTree}$ recursive resumption |
| RA-4 | bilimit projections, pointwise in initial state |
| RA-5 | exact `get`/`put` transition |
| RA-6 | state-indexed admissible relation |
| RA-7 | pointwise continuous handler functional |
| RA-8 | Level 2: finite boundary and divergence |

No Writer-prefix operation appears in the proof.  This is evidence that
`RecursiveBaseAdequacy` captures a genuinely shared structure.

## 8. Remaining distinction

Writer and State both validate the package, but they make different choices
invisible at Level 2:

- Writer forgets an infinite output stream before divergence;
- State forgets transient states before divergence;
- State additionally fixes global, nonbacktracking resumption interaction.

These choices belong to `BaseObservation` and `HandlerInteraction`, not to the
unordered free-row theorem.
