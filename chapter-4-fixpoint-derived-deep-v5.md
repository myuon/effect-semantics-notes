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
f:A\to(B!L).
$$

Operational unfolding is standard CBV.  A trace annotation remains a safety
upper bound on every finite execution prefix; it need not imply termination or
bound the number of repetitions.

## 2. Semantic requirements for recursion

The finite tree of Chapters II–III is replaced by a recursive resumption
object, schematically

$$
\mathsf R_{T,L}A
\cong
T\bigl(A+\Sigma_L(\mathsf R_{T,L}A)\bigr).
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

For another interface $\Gamma$, derivation of fully conventional forwarding
requires the shallow interface to expose its fallback continuation as well:

```text
other op_Gamma(p,k) ->
  forward op_Gamma(p, fun r -> loop (k r))
```

If Chapter III instead uses the stricter rule that forwarding terminates the
handler, the derived construct searches only across matching resumptions and
is not a conventional deep handler across intervening interfaces.  The main
calculus therefore includes the explicit `other` continuation form, while the
terminating-forward variant remains a definable restricted handler.

## 4. Ordered trace action

For affine deep clauses, recursive reinstallation repeatedly applies the
Chapter-III law.  On a finite trace,

$$
b_0\cdot\Delta\cdot b_1\cdot\Delta\cdots
\Delta\cdot b_n
$$

is transformed into

$$
b_0\cdot e'_1\cdot b_1\cdot e'_2\cdots
e'_n\cdot b_n.
$$

Nonmatching free events are forwarded in place, with the recursive handler
retained in their continuations.  For infinite behavior, the sound statement
is prefix based: every finite observable prefix agrees with some finite
unfolding of the recursive definition.

## 5. Elimination theorem shape

Assume:

1. the input trace language contains only well-typed $\Delta$ requests;
2. the handler is exhaustive for $\Delta$;
3. handler clauses do not themselves emit $\Delta$;
4. forwarding reinstalls the recursive loop;
5. the fixed point is interpreted by the selected operationally adequate
   recursion principle.

Then no finite outward trace of the derived deep-handled program contains an
unhandled $\Delta$ event.  The program may still diverge, raise a base
exception, or produce an infinite trace of other effects.  Elimination is a
safety property, not a termination theorem.

## 6. Preservation theorem program

Chapter IV asks which certificates from Chapters I–III lift through the fixed
point:

- type preservation and effect-aware progress;
- old-program conservativity;
- prefix-closed ordered trace soundness;
- continuity/iteration compatibility of the free-operation extension;
- admissible logical-relation lifting;
- finite observation adequacy;
- divergence and productive-trace adequacy, stated separately;
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
4. one program with an intervening nonmatching free operation, testing the
   explicit forwarding continuation.

