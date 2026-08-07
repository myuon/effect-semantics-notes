# Chapter IV — recursion, derived deep handling, and programs

## Status

**Operational development over `ShallowCert`.**  Fixpoint is added to the
computation language.  Deep handling remains derived syntax.

## 1. Recursive functions

Add

```text
let rec f(x : A) : B ! e = M in N
```

with the rule

$$
\frac{
 \Gamma,f:A\to(B!e),x:A\vdash M:B!e
 \qquad
 \Gamma,f:A\to(B!e)\vdash N:C!d
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
certificate.  Exact ordered grades require an affine/linear restriction or a
quantitative extension; they do not follow from recursion alone.
