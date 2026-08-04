# Extensibility question v2

## Status

**Current research program. Definitions are provisional; the question is fixed.**

## Central question

> **What structure makes an effectful language extensible by user-defined operations and handlers?**

More explicitly, suppose a base language already has:

- a static effect discipline;
- operational semantics;
- a monadic, graded-monadic, indexed, or otherwise compositional denotational semantics;
- an observation theorem, simulation, adequacy theorem, or logical relation.

When can we add user-defined free operations and handlers while preserving those structures and results?

The target is not a new language merely having effects and handlers.  The target is an **extension theorem and a boundary map**.

## Why “arbitrary effect system” is too coarse

An effect annotation, a computation model, and a runtime decomposition are different data.

1. A static annotation says what is approximated: sets, rows, traces, counts, capabilities, or protocols.
2. A monad or graded monad says how computations compose.
3. A handler needs an intensional view exposing return, operation, and continuation structure.

For an opaque monad $T$, the maps

$$
\eta:X\to TX,
\qquad
\mu:TTX\to TX
$$

do not provide an inverse decomposition

$$
TX\longrightarrow X+\sum_{\operatorname{op}}P_{\operatorname{op}}\times(R_{\operatorname{op}}\to TX).
$$

Therefore the input of the theorem must be a structured [base semantic package](base-semantic-package-v2.md), not merely the assertion that some effect system or monad exists.

## Proposed extension problem

Let $\mathcal B$ be a base semantic package and $\Sigma$ a signature of new first-order operations.  Seek a partial construction

$$
\operatorname{Ext}_{\Sigma}(\mathcal B,h)
$$

parameterized by a handler fragment $h$:

- operation generation only;
- one-shot handling;
- deep, single-resumption handling;
- deep, multi-shot handling;
- later, scoped or higher-order handling.

“Partial” is intentional.  The construction may require additional capabilities from $\mathcal B$, and failure to satisfy them should produce a counterexample or impossibility statement rather than an artificial top effect.

## Candidate theorem shape

:::{prf:conjecture} Capability-indexed extension theorem
:label: conj-capability-extension

For every base package $\mathcal B$ satisfying capability profile $C_h$, and every first-order signature $\Sigma$, there is an extension $\widehat{\mathcal B}=\operatorname{Ext}_{\Sigma}(\mathcal B,h)$ such that a specified property package $P_h$ is preserved.  If a capability in $C_h$ is removed, either a weaker property package is obtained or there is a counterexample base package.
:::

The intended contribution is the correspondence

$$
\text{handler fragment}
\quad\leftrightarrow\quad
\text{required base capabilities}
\quad\leftrightarrow\quad
\text{preserved properties}.
$$

## Initial hypotheses

The following are working hypotheses, not established results.

1. **Free generation is weakest.** A monadic base is often enough to add uninterpreted first-order operations through a free transformer or interaction layer.
2. **Base-pure one-shot handling is broadly portable.** It should preserve the base grade under relatively weak assumptions.
3. **Deep single-resumption handling needs algebraicity and a stable notion of forwarding.**
4. **Multi-shot handling needs duplicability.** It can repeat future base effects and is not sound for every resource or one-shot base semantics.
5. **Base-effectful clauses need effect interaction structure.** An unordered free row alone cannot determine how often or where clause effects are inserted into a noncommutative base grade.
6. **Higher-order or scoped effects require more than a first-order free-monad interface.**

## First research cycle

The first cycle is deliberately small.

1. Fix the known baseline: recursion-free fine-grain CBV STLC, unordered rows, exhaustive deep handlers.
2. State and prove its type safety, unhandled-effect safety, elimination, and tree adequacy.
3. Replace the trivial base by a parameterized base semantic package while keeping handler clauses base-pure.
4. Identify exactly which baseline proofs lift structurally.
5. Add base-effectful clauses and search for the first counterexample.
6. Compare remedies: commutative/idempotent base effects, iteration, counts, or ordered trace refinement.

The [extension audit](extension-audit-v2.md) records the result of each step.

## Success criteria

This direction succeeds even if no single maximal theorem exists.  A useful result may be:

- a general positive extension theorem under explicit assumptions;
- a minimal counterexample showing a missing assumption is necessary;
- a hierarchy of handler fragments by required base structure;
- an abstraction theorem relating runtime trees, ordered traces, counts, and unordered rows;
- a reusable proof recipe for an existing language designer considering handlers.

