# Base calculus examples v1

## 1. Two levels of execution

[Base calculus v1](base-calculus-v1.md) のinternal reductionを

$$
M\longrightarrow M'
$$

と書く。このrelationはpure computationを進めるが、露出したbase operation

$$
\beta(V;y.M)
$$

を勝手に実行しない。したがってcalculus単体での最終観測は

$$
\mathsf{return}\;V
$$

またはbase-operation requestである。

具体的な`Writer`や`State`の結果も計算したい場合は、configuration

$$
\langle M,s\rangle
$$

を使い、base machineの状態 $s$ とoperationへの応答ruleを追加する。以下ではinternal stepsとmachine stepsを区別して表示する。

## 2. Example A — Pure return and function application

Program:

```text
let f <- return (fun x -> return x) in
f true
```

First, `R-Let-Return`:

```text
--> (fun x -> return x) true
```

Then `R-Beta`:

```text
--> return true
```

Hence

$$
M\longrightarrow^*\mathsf{return}\;\mathsf{true}.
$$

The effect is pure:

$$
\Gamma\vdash M:\mathsf{Bool}!1.
$$

## 3. Example B — Exposing one base request

Assume

$$
\mathsf{tell}:\mathsf{String}\to1
$$

with grade $|\mathsf{tell}|=w$. Consider:

```text
let x <- tell("a"; u. return true) in
return x
```

By `R-Let-Base`:

```text
-->
tell("a"; u.
  let x <- return true in
  return x)
```

This is a head form. Internal reduction stops here: the `let` inside the suspended continuation is not evaluated before `tell` receives a result.

The type-and-effect derivation gives

$$
\mathsf{tell}(\text{"a"};u.\mathsf{return}\;\mathsf{true})
:\mathsf{Bool}!(w\cdot1)=\mathsf{Bool}!w
$$

and the whole program has effect

$$
w\cdot1=w.
$$

## 4. Writer machine

Instantiate the base machine state by a log

$$
\ell\in\mathsf{List}(\mathsf{String}).
$$

Internal steps lift to configurations:

$$
\frac{M\longrightarrow M'}
{\langle M,\ell\rangle\longrightarrow_W\langle M',\ell\rangle}.
$$

The Writer response rule is

$$
\langle\mathsf{tell}(s;u.M),\ell\rangle
\longrightarrow_W
\langle M[*/u],\ell\mathbin{+\!+}[s]\rangle.
\tag{W-Tell}
$$

Here $+\!+$ is list concatenation.

### Example C — Two ordered writes

Program:

```text
let x <- tell("a"; u. return true) in
tell("b"; v. return x)
```

Start with an empty log:

```text
< let x <- tell("a"; u. return true) in
    tell("b"; v. return x),
  [] >
```

`R-Let-Base` exposes the first request:

```text
-->W
< tell("a"; u.
    let x <- return true in
    tell("b"; v. return x)),
  [] >
```

`W-Tell` records `"a"` and resumes the continuation:

```text
-->W
< let x <- return true in
    tell("b"; v. return x),
  ["a"] >
```

`R-Let-Return` substitutes `true` for `x`:

```text
-->W
< tell("b"; v. return true),
  ["a"] >
```

The second `W-Tell` step gives:

```text
-->W
< return true,
  ["a", "b"] >
```

Thus the result value is `true` and the observable log is exactly

$$
[\text{"a"},\text{"b"}].
$$

The effect is

$$
w\cdot w.
$$

The order in the operational log agrees with the left-to-right order of the monoid product.

## 5. State machine

Use a Boolean store $s\in\mathsf{Bool}$ and operations

$$
\mathsf{get}:1\to\mathsf{Bool},
\qquad
\mathsf{put}:\mathsf{Bool}\to1.
$$

Machine rules:

$$
\langle\mathsf{get}(*;x.M),s\rangle
\longrightarrow_S
\langle M[s/x],s\rangle,
\tag{S-Get}
$$

$$
\langle\mathsf{put}(s';u.M),s\rangle
\longrightarrow_S
\langle M[*/u],s'\rangle.
\tag{S-Put}
$$

As with Writer, internal reductions lift without changing the store.

### Example D — Read, branch, then write

Program:

```text
get(*; x.
  if x then
    put(false; u. return x)
  else
    put(true; u. return x))
```

Run it from store `true`:

```text
< get(*; x.
    if x then
      put(false; u. return x)
    else
      put(true; u. return x)),
  true >
```

`S-Get` substitutes the current state:

```text
-->S
< if true then
    put(false; u. return true)
  else
    put(true; u. return true),
  true >
```

`R-If-True`:

```text
-->S
< put(false; u. return true), true >
```

`S-Put`:

```text
-->S
< return true, false >
```

The returned value is the old state `true`; the final store is `false`.

Starting from `false` instead gives

```text
< return false, true >
```

so this program returns the old bit and flips the stored bit.

If $|\mathsf{get}|=r$ and $|\mathsf{put}|=w$, its effect is

$$
r\cdot w.
$$

In general this need not equal $w\cdot r$: the annotation preserves operational order.

## 6. Example E — Why the current base effect is an upper bound

Assume

$$
1\leq w.
$$

Consider:

```text
if false then
  tell("unreachable"; u. return true)
else
  return false
```

The then branch has effect $w$. The else branch initially has effect $1$, then `T-Sub` assigns it effect $w$. Hence `T-If` assigns the whole expression effect $w$.

Operationally, however,

```text
if false then
  tell("unreachable"; u. return true)
else
  return false

--> return false
```

No `tell` request occurs. Therefore the judgment

$$
\Gamma\vdash M:\mathsf{Bool}!w
$$

does not claim that $w$ definitely occurs. It states that $w$ is a safe upper approximation of possible base effects.

This example is the first decision test for Stage 0. If the intended base system must instead record exact traces, `T-Sub` and the branching rule must be changed before adding free operations.

## 7. Summary of observable outcomes

| Example | Internal head/result | Concrete machine result | Effect |
|---|---|---|---|
| A: pure function | `return true` | — | $1$ |
| B: one request | exposed `tell "a"` | Writer: `return true`, log `["a"]` | $w$ |
| C: two writes | exposed first `tell` | Writer: `return true`, log `["a","b"]` | $w\cdot w$ |
| D: state flip | exposed `get` | from `true`: value `true`, state `false` | $r\cdot w$ |
| E: unreachable write | `return false` | Writer log remains empty | upper bound $w$ |

