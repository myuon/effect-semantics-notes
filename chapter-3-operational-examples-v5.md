# Chapter III — direct shallow-handler semantics and programs

:::{admonition} Lean correspondence — Chapter III
:class: tip
**Lean checked.** The finite semantic handler is [`FreeExtension.shallow`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow#doc); its matching and forwarding equations are [`shallow_match`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow_match#doc) and [`shallow_forward`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.shallow_forward#doc). [Full mapping](review-guide.md#chapter-iii-shallow-handlers).
:::

## Status

**Operational development.**  This page adds shallow handlers to the
recursion-free language carrying `FreeCert`.

## 1. General handler syntax

For an interface $\Delta$, write

```text
shallow_Delta M with {
  return x  -> Hret;
  op_i(p,k) -> Hi
}
```

Every operation in $\Sigma(\Delta)$ has a matching clause.  In an operation
clause,

$$
k:R_i\xrightarrow{e}A
$$

is the captured continuation of the handled computation.  It is supplied by
the handler reduction rule, not by the source operation.

A request from another interface is forwarded with a continuation that retains
this handler.  The handler therefore searches through unrelated interfaces
until it meets the first matching $\Delta$ request or a return.

## 2. Handler evaluation contexts

The scrutinee is evaluated first:

$$
\mathcal H::=[]
\mid\mathsf{shallow}_\Delta\ \mathcal H\ \mathsf{with}\ h.
$$

Internal reductions and base-machine transitions occur inside the handler.
Thus the handler is transparent to base computation until the scrutinee
returns or exposes a free request.

## 3. Direct reduction rules

For a returned value,

$$
\mathsf{shallow}_\Delta(\mathsf{return}\,V,h)
\longrightarrow H_{\mathsf{ret}}[V/x].
\tag{SH-Ret}
$$

For a handled operation $i\in J$,

$$
\begin{aligned}
&\mathsf{shallow}_\Delta
  (\mathcal E[\mathsf{op}_{\Delta,i}(V)],h)\\
&\quad\longrightarrow
H_i\left[
V/p,
(\lambda r.\mathcal E[\mathsf{return}\,r])/k
\right].
\end{aligned}
\tag{SH-Match}
$$

The continuation contains no copy of $h$.  If the clause calls it, later free
requests are outside this handler.

For $\Gamma\neq\Delta$, or $\Gamma=\Delta$ with $j\notin J$,

$$
\begin{aligned}
&\mathsf{shallow}_\Delta
 (\mathcal E[\mathsf{op}_{\Gamma,j}(V)],h)\\
&\quad\leadsto
\mathsf{request}_{\Gamma,j}
\left(V,\lambda r.\mathsf{shallow}_\Delta
(\mathcal E[\mathsf{return}\,r],h)\right).
\end{aligned}
\tag{SH-Forward}
$$

The request remains visible to an outer handler, but resuming it continues the
search for a handled operation. Only a selected clause receives a bare
continuation and ends this handler. Existing examples use the exhaustive case
$J=I_\Delta$ unless stated otherwise.

## 4. Affine response fragment

The response-only notation

```text
with { op_i(p) -> R_i }
```

elaborates to

```text
op_i(p,k) -> let r <- R_i in k r
```

with identity return and transparent forwarding.  It invokes $k$ exactly once and
does not expose it to user code.

Suppose the scrutinee has upper bound, with $b$ containing no $\Delta$,

$$
b\cdot\Delta\cdot e
$$

and every response computation has bound $e'$.  The matching path has output
bound

$$
b\cdot e'\cdot e.
$$

The annotation may overapproximate a path on which $\Delta$ is absent.  That
path is bounded by $b\cdot e$, which is below the same output when $1\leq e'$.

## 5. Writer calculation

Handle the Chapter-II program

```text
shallow_Ask (
  let _ <- tell_a(*) in
  let x <- ask("continue?") in
  let _ <- tell_b(*) in
  return x
) with {
  ask(q) ->
    let _ <- tell_h(*) in
    return true
}
```

Writer first produces log `[a]`, then exposes `ask`.  `SH-Match` gives

```text
let r <- (let _ <- tell_h(*) in return true) in
let _ <- tell_b(*) in
return r
```

which finishes with result `true` and log

$$
[a,h,b].
$$

The effect transformation is

$$
[a]\cdot\Delta\cdot[b]
\longmapsto
[a]\cdot[h]\cdot[b].
$$

### Two matching requests

For

```text
shallow_Ask (
  let x <- ask("first") in
  let y <- ask("second") in
  return y
) with { ask(q) -> return true }
```

only the first request is handled.  After substituting `true`, the result is

```text
let y <- ask("second") in return y
```

and the second request is exposed.  Statically,

$$
\Delta\cdot\Delta
\longmapsto
1\cdot\Delta=\Delta.
$$

This is the observable difference from deep handling.

## 6. State calculation

Consider

```text
shallow_Choose (
  let old <- get(*) in
  let answer <- choose(old) in
  let _ <- put(answer) in
  return old
) with {
  choose(p) -> return (not p)
}
```

From store `true`, `get` returns `true`; the handler responds `false`; the bare
continuation executes `put(false)` and returns the old value.  The final
configuration is

$$
\langle\mathsf{return}\,\mathsf{true},\mathsf{false}\rangle.
$$

The upper-bound transformation is

$$
\mathsf{read}\cdot\Delta\cdot\mathsf{write}
\longmapsto
\mathsf{read}\cdot\mathsf{write}.
$$

If the response clause itself performs a write before invoking $k$, its effect
appears between the prefix and continuation effects.

## 7. Exception calculation

For

```text
shallow_Ask (
  let _ <- raise_boom(*) in ask("unreachable")
) with { ask(q) -> return true }
```

the base machine reaches `error(boom)` before any free request.  No operation
clause runs.

For

```text
shallow_Ask (ask("reachable")) with {
  ask(q) -> raise_boom(*)
}
```

`SH-Match` selects the clause and the whole program terminates at
`error(boom)`.  The possible effect changes from $\Delta$ to
$\mathsf{raise}$.

## 8. Transparent unrelated-interface forwarding

Let `choose` belong to $\Gamma\neq\Delta=\mathsf{Ask}$.  In

```text
shallow_Ask (
  let x <- choose(false) in
  ask("later")
) with { ask(q) -> return true }
```

the first exposed request is `choose`.  `SH-Forward` forwards it with the
pending `Ask` handler in its continuation.  If an outer handler supplies a
response, the subsequent `ask` is caught.  After that match, the clause's bare
continuation is no longer protected.  This is searching shallow behavior, not
deep handling.

## 9. Partial same-interface forwarding

Let one interface $\Delta$ contain both

$$
\mathsf{tick}:1\to1,
\qquad
\mathsf{ask}:\mathsf{String}\to\mathsf{Bool},
$$

and take $J=\{\mathsf{ask}\}$. In

```text
shallow_Delta (
  let _ <- tick(*) in
  ask("later")
) with { ask(q, k) -> k true }
```

the first request `tick` has no clause. It is forwarded with the partial
handler retained:

```text
tick(*; fun _ -> shallow_Delta (ask("later")) with h)
```

After an outer handler responds to `tick`, the pending handler catches `ask`
and invokes its bare continuation once. Operational and tree semantics agree
without an exhaustive clause table.

At interface-level granularity the sound result still contains a $\Delta$
factor for the forwarded `tick`. Thus this example validates safety and
commutation but refutes unconditional interface elimination by a partial
handler.
