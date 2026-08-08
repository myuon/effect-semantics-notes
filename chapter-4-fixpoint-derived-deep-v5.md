# Chapter IV — fixed points and derived deep handlers

## Status

**Research specification.**  This chapter adds computation-level recursion.
Deep handlers are then defined from the Chapter-III shallow construct; they are
not primitive syntax.

## 1. Fixpoint discipline

We do not add an unrestricted pure operator

$$
\mathsf{fix}_A:(A\to A)\to A
$$

to every value type.  Recursion lives in the computation layer, for example as

```text
let rec f(x : A) = M in N
```

with effectful function type

$$
f:A\xrightarrow{e}B.
$$

Operational unfolding is standard CBV.  An effect annotation remains a may
upper bound; it does not imply termination or bound the number of repetitions.

## 2. Semantic requirements for recursion

The finite tree of Chapters II–III is replaced by a recursive resumption
object, schematically

$$
\mathsf R_{T,e}A
\cong
T\bigl(A+\Sigma_e(\mathsf R_{T,e}A)\bigr).
$$

The chosen base model must supply an explicit recursion principle, such as:

- a pointed $\omega$-cpo model with locally continuous constructors and least
  fixed points;
- a complete Elgot iteration operator satisfying the required compatibility;
- guarded recursion with a proved correspondence to operational unfolding.

Monad laws alone do not supply this structure.  Logical relations used for
adequacy must be admissible or closed under the selected approximation rule.

## 3. Deriving deep handling

Let $h$ contain a return clause and operation bodies parameterized by a
resumption.  Define

```text
deep_Delta M with h :=
  (fix loop. fun m ->
     shallow_Delta m with {
       return x  -> h.return x;
       op_i(p,k) -> h.op_i(p, fun r -> loop (k r))
     }) M
```

The shallow continuation `k` does not contain the handler.  The recursive
wrapper `loop` reinstalls it after every resumption.  This is exactly the usual
deep-handler behavior.

The same definition works for a partial handled set $J$: operations outside
$J$ are forwarded with the search retained, while resumptions of clauses in
$J$ are recursively wrapped. This gives a partial deep handler. Exhaustiveness
is needed later only to conclude interface-level elimination.

Chapter III already forwards every unhandled request with the shallow
handler retained in its continuation.  Therefore the only additional wrapping
needed to obtain deep behavior is in selected matching resumptions. Shallow
and deep differ exactly on the continuation of a caught operation.

## 4. Ordered effect action

For affine deep clauses, recursive reinstallation repeatedly applies the
Chapter-III law.  For a finite ordered effect bound, with each $b_i$
$\Delta$-free,

$$
b_0\cdot\Delta\cdot b_1\cdot\Delta\cdots
\Delta\cdot b_n
$$

is transformed into

$$
b_0\cdot e'_1\cdot b_1\cdot e'_2\cdots
e'_n\cdot b_n.
$$

Nonmatching free operations are forwarded in place, with the recursive handler
retained in their continuations.  With recursion, a finite word may no longer
bound arbitrarily many repetitions; Chapter IV must therefore choose an
iteration-closed effect algebra or an explicit closure $e^*$.

## 5. Elimination theorem shape

Assume:

1. the input effect bound covers all possible $\Delta$ requests;
2. the handler is exhaustive for $\Delta$;
3. handler clauses do not themselves emit $\Delta$;
4. transparent forwarding preserves the pending shallow handler;
5. the fixed point is interpreted by the selected operationally adequate
   recursion principle.

Then the outward effect bound of the derived deep-handled program may omit
$\Delta$, and operational progress never exposes an unhandled $\Delta$ request
outside the derived handler.  The program may still diverge or raise a base
exception.  Elimination is a safety property, not a termination theorem.

## 6. Preservation theorem program

Chapter IV asks which certificates from Chapters I–III lift through the fixed
point:

- type preservation and effect-aware progress;
- old-program conservativity;
- ordered upper-bound effect safety under unfolding;
- continuity/iteration compatibility of the free-operation extension;
- admissible logical-relation lifting;
- finite observation adequacy;
- divergence adequacy, stated separately;
- equivalence between the derived program and the recursive semantic handler
  fold.

The last equivalence is the central new bridge.  It prevents us from assuming a
primitive deep handler in the denotation after claiming that deep behavior was
derived in the source language.

## 7. Concrete proof order

Before a general theorem, calculate:

1. recursive Writer with repeated handled operations;
2. recursive State where resumptions revisit updated stores;
3. Exception where a base exception cuts off further reinstallation;
4. one program with an intervening nonmatching free operation, testing
   transparent forwarding.

The full Chapter-IV cycle is developed in:

- [Operational rules and concrete programs](chapter-4-operational-examples-v5.md);
- [Recursive denotational semantics](chapter-4-denotational-v5.md);
- [Proofs and `DeepCert`](chapter-4-certificate-v5.md).
