# Recursive behavior: deriving deep handling from shallow handling

:::{admonition} Lean correspondence — Chapter IV
:class: tip
**Lean checked.** The executable finite-fuel resumption evaluator is [`genericRunFuel`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericRunFuel#doc), and [`genericRunFuel_eq_iterate`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericRunFuel_eq_iterate#doc) identifies it with finite semantic iteration. The Writer request/resume/`tell` calculation reaches the LFP in [`example_limit_true`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveWriter.example_limit_true#doc).
:::

## Status

**Operational development over `ShallowHandlerPackage`.**  Fixpoint is added to the
computation language.  Deep handling remains derived syntax.

## 1. Recursive functions

Add

```text
let rec f(x : A) : B ! e = M in N
```

with the rule

$$
\frac{
 \Gamma,f:A\xrightarrow{e}B,x:A\vdash M:B!e
 \qquad
 \Gamma,f:A\xrightarrow{e}B\vdash N:C!d
}{
 \Gamma\vdash\mathsf{let\ rec}\ f(x)=M\ \mathsf{in}\ N:C!d
}.
$$

Calling the recursive function unfolds its body in the ordinary CBV way.  The
annotation $e$ bounds one unfolding of the body; it does not bound the number
of unfoldings and does not assert termination.

## 2. Deep handling as a program

Let `shallow` be the general Chapter-III form exposing a bare continuation.
Define

```text
deep_Delta M with h :=
  let rec loop(m) =
    shallow_Delta m with {
      return x  -> h.return(x);
      op_i(p,k) -> h.op_i(p, fun r -> loop(k(r)))
    }
  in loop(M)
```

There is no primitive deep reduction rule.  One shallow step captures `k`;
the recursive call reinstalls the handler around `k(r)`.  Nonmatching
operations already retain the Chapter-III shallow handler automatically.

## 3. Writer: finitely many requests

Let `Tick` contain $\mathsf{tick}:1\to1$ and define

```text
ticks(0) = return ()
ticks(n+1) = tick(); tell("a"); ticks(n)
```

Use the clause

```text
tick(_,k) -> tell("h"); k(())
```

For `ticks(2)`, derived expansion gives

```text
tell("h"); tell("a");
tell("h"); tell("a");
return ()
```

and the log is $[h,a,h,a]$.  Every call of the recursive continuation is
again protected by the shallow handler.

For each fixed numeral $n$, the ordered input word

$$
(\Delta\cdot a)^n
$$

becomes $(h\cdot a)^n$.  A single type for arbitrary $n$ instead needs a
closure such as $(\Delta\cdot a)^*$; a finite word is not sufficient.

## 4. Productive divergence

```text
forever() = tick(); tell("a"); forever()
```

The derived handler repeatedly produces the prefix
$h,a,h,a,\ldots$ and never exposes `Tick`.  In a partial Writer model
$(W\times A)_\bot$, this computation denotes $\bot$: the model observes
divergence but not the infinite log.  Infinite-trace adequacy therefore needs
a richer base observation and is not implied by ordinary adequacy.

## 5. State

Handle `ticks(n)` with

```text
tick(_,k) ->
  x <- get();
  put(x + 1);
  k(())
```

Starting at $s$, the result is $((),s+n)$.  The continuation sees the state
left by the previous clause.  Deep reinstallation neither copies nor restores
state.

## 6. Exception

With `tick(_,k) -> raise Stop`, the first request aborts without resumption.
With `tick(_,k) -> k(())`, an old exception in the tail propagates normally.
Thus eliminating $\Delta$ means that no unhandled $\Delta$ escapes; it does
not mean that the computation returns.

## 7. Forwarding across another interface

In

```text
x <- ask(); tick(); return x
```

a shallow or deep `Tick` handler forwards `ask` with the pending handler in its
continuation.  After an outer handler answers `ask`, the later `tick` is caught.
Deep handling additionally wraps the matching resumption as

```text
fun r -> loop(k(r))
```

so subsequent `Tick` requests are caught as well.

## 8. Multi-shot boundary

A general clause may invoke its rehandled continuation twice.  For Writer or
State this duplicates the tail and its base effects in model-specific order.
The basic theorem permits this only through an explicit handler effect
package.  Exact ordered grades require an affine/linear restriction or a
quantitative extension; they do not follow from recursion alone.

## 9. Partial deep handling does not eliminate an interface

Let one interface $\Delta$ contain two operations

$$
\mathsf{tick}:1\to1,
\qquad
\mathsf{tock}:1\to1,
$$

and let the handled set be only $J=\{\mathsf{tick}\}$.  Write $h_J$ for

```text
return x  -> return x
tick(_,k) -> tell("h"); k(())
```

where the omitted `tock` branch means transparent forwarding, not abortion.
Consider

```text
rounds(0)   = return ()
rounds(n+1) = tick(); tock(); rounds(n)
```

For `deep_Delta rounds(2) with h_J`, the first `tick` is caught and its
resumption is wrapped again:

```text
deep_Delta rounds(2) with h_J
  --> tell("h"); deep_Delta (tock(); rounds(1)) with h_J
  --> tell("h"); tock((), fun _ -> deep_Delta rounds(1) with h_J)
```

The last term is an exposed `tock` request.  It is not a stuck error: it is a
boundary offered to an enclosing handler, and its continuation still contains
the partial deep handler. If an enclosing **derived-deep** `tock` handler
writes `"o"` and resumes at each request, evaluation continues as

```text
tell("h"); tell("o");
tell("h"); tell("o");
return ()
```

with Writer log $[h,o,h,o]$.  Hence all `tick` requests are handled at every
recursive depth, while `tock` remains observable at every round.

This example separates two claims:

1. `DerivedDeepPackage` is meaningful for a partial set $J$: fixpoint
   reinstallation repeatedly catches every selected operation.
2. `DeepElimination(\Delta)` is false: since `tock` belongs to the same interface,
   the interface-level grade $\Delta$ must remain in the outward upper bound.

An operation-granular effect algebra could express elimination of `tick` while
retaining `tock`.  The present interface-granular algebra deliberately makes
only the weaker claim.
