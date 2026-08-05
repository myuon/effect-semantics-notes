# Recursion preservation v2

## Status

**Preservation audit after adding effectful recursive functions.**  This page
states what survives unchanged, what needs stronger hypotheses, and what is
lost.

## 1. Result matrix

| Property | Recursion-free | With general recursion |
|---|---|---|
| deterministic decomposition | yes | preserved |
| type/row preservation | yes | preserved |
| effect-aware progress | yes | preserved |
| empty-row request safety | yes | preserved, but divergence allowed |
| deep discharge of $\Delta$ | yes | preserved for every reachable finite prefix |
| old syntax operational conservativity | yes | preserved |
| strong/head normalization | yes under former hypotheses | false |
| finite initial resumption | sufficient | only terminating fragment |
| handler definition | initial fold | Elgot iteration or guarded corecursion |
| monad morphism lifting | monad morphism | must also preserve iteration/limits |
| logical relation lifting | structural induction | admissible, step-indexed, or guarded relation |
| terminating adequacy | conditional | preserved |
| divergence adequacy | unnecessary | new substantial obligation |
| exact infinite base traces | unnecessary | requires trace-sensitive base model |

## 2. Operational preservation theorem

:::{prf:theorem} Unordered recursive safety extension
:label: thm-unordered-recursive-safety-v2

Under `BaseSafety` extended with a typed deterministic recursive-unfolding rule,
adding first-order free operations and exhaustive deep handlers preserves:

- relative determinism;
- type and unordered-row preservation;
- effect-aware progress;
- absence of escaping new requests at empty row;
- deep discharge of a handled interface;
- operational conservativity of the old recursive language.
:::

No normalization or denotational assumption is needed.  Deep discharge is a
safety property: if execution is infinite, every finite reachable state still
has the discharged outward row.

## 3. Recursive denotational theorem candidate

Assume:

1. a recursive base semantics $T_\bot$ with complete Elgot iteration, or an
   equivalent pointed locally continuous model;
2. existence of the coalgebraic resumption carrier
   $\mathsf{CRes}_{T_\bot,\rho}$;
3. iteration-compatible interpretations of base primitives and handler
   clauses;
4. an operational observation relation covering return, base outcome,
   unhandled request, and divergence.

:::{prf:conjecture} Recursive unordered extension theorem
:label: conj-recursive-unordered-extension-v2

Under these assumptions, the unordered free extension:

- is a monad with coherent row weakening;
- embeds the recursive base semantics;
- interprets recursive functions by iteration;
- interprets exhaustive deep handlers;
- preserves one-step soundness and finite-observation discharge;
- lifts iteration-preserving base morphisms;
- lifts admissible/guarded logical relations;
- preserves terminating adequacy and, with a divergence-reflecting relation,
  divergence adequacy.
:::

This is the recursion-aware replacement for the initial-algebra main theorem.

## 4. Changed proof methods

### Soundness

One-step soundness gains one case:

$$
\llbracket(\mathsf{rec}\ f(x).M)V\rrbracket
=
\llbracket M[\mathsf{rec}\ f(x).M/f,V/x]\rrbracket,
$$

which is exactly the unfolding law of iteration.  The old operation and handler
cases are otherwise unchanged.

### Adequacy

Termination can no longer be used to normalize every program.  Adequacy must be
proved by one of:

- approximation by finite unfoldings;
- admissible domain logical relations;
- step-indexed/guarded logical relations;
- coinductive simulation or weak bisimulation.

Guarded interaction trees have been used to give sound and computationally
adequate semantics to a PCF-like language with effects, showing that this proof
route is realistic rather than merely aspirational; see [Modular Denotational
Semantics for Effects with Guarded Interaction
Trees](https://arxiv.org/abs/2307.08514).

### Morphisms

A plain monad morphism need not preserve the chosen meaning of recursion.  The
required equation is

$$
q(f^\dagger)=(qf)^\dagger.
$$

Only iteration-preserving/continuous morphisms receive the recursive lifting
theorem.

### Relations

The least structural relation on finite trees is insufficient for infinite
behavior.  The base relation must contain bottom, be closed under approximation
limits, or be guarded/step-indexed.  Handler preservation then follows by
admissible fixed-point induction or guarded Löb induction rather than ordinary
tree induction.

## 5. Adequacy levels

It is useful to state three separate results.

### Level 1: terminating adequacy

If evaluation reaches return, base outcome, or request, the denotation has the
corresponding observation, and conversely.  This is closest to the current
conditional theorem and should transfer first.

### Level 2: may-divergence adequacy

Operational divergence corresponds to semantic bottom or an infinite `Tau`
behavior.  This needs base computational adequacy plus a recursion-specific
logical relation.

### Level 3: productive infinite-trace adequacy

An execution may perform infinitely many observable base/free actions without
returning.  Preserving the exact trace requires a coinductive observation model
that keeps these actions visible.  The partial Writer/State models in the
previous page do not provide this level.

The generic main theorem should target Levels 1 and 2.  Level 3 belongs to a
stronger `BaseObservation` package.

## 6. Concrete examples

### Silent loop

```text
loop = rec f(u). f(u)
```

Row: $\varnothing$.  Operationally safe but divergent.  Denotation: bottom or
infinite `Tau`.

### Finite-or-infinite requests

```text
rec f(n).
  if n == 0 then return ()
  else let _ <- opDelta() in f(n - 1)
```

For ordinary natural input it emits finitely many requests; a more general
recursive control condition may emit infinitely many.  In all cases the row is
$\{\Delta\}$.

### Divergence under a deep handler

```text
handle loop() with hDelta
```

No $\Delta$ escapes, but the program still diverges.  Elimination is therefore
orthogonal to termination.

### Productive handled loop

```text
rec f(u).
  let _ <- opDelta() in f(u)
```

An exhaustive deep handler may transform every $\Delta$ into a Writer action.
This yields an infinite output behavior.  A bottom-only Writer semantics sees
only divergence; a visible coinductive Writer semantics distinguishes the
infinite output trace.

## 7. Recommended theorem architecture

```text
Layer 0: recursive BaseSafety
    -> operational safety and deep discharge

Layer 1: complete-Elgot/continuous base semantics
    -> fixpoint interpretation and recursive resumption monad

Layer 2: divergence-reflecting observation/logical relation
    -> computational adequacy

Layer 3: optional visible coinductive base observations
    -> productive infinite-trace adequacy
```

This preserves the broad unordered theorem without forcing every base effect to
expose infinite traces.  The extra assumptions are requested only for the
stronger recursive conclusions.
