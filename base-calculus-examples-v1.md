# Base calculus examples v1

## 1. Operations do not contain continuations

In [Base calculus v1](base-calculus-v1.md), a base operation is a computation

$$
\beta(V):R_\beta!|\beta|.
$$

For example,

$$
\mathsf{tell}(\text{"a"}):1!w.
$$

The operation takes only its parameter. A subsequent computation is written with ordinary `let`:

```text
let u <- tell("a") in
M
```

The continuation is therefore not part of `tell`. Metatheoretically, the surrounding evaluation context

```text
let u <- [-] in M
```

remembers what to do after the operation returns.

Internal reduction is written $M\longrightarrow M'$. It reduces pure computation, but it does not execute a base operation. A request inside an evaluation context has the form

$$
\mathcal E[\beta(V)].
$$

A concrete base machine responds with a value $W:R_\beta$ by replacing the request with $\mathsf{return}\;W$:

$$
\mathcal E[\beta(V)]
\rightsquigarrow
\mathcal E[\mathsf{return}\;W].
$$

## 2. Example A — Pure return and function application

```text
let f <- return (fun x -> return x) in
f true
```

By `R-Let-Return` and then `R-Beta`:

```text
--> (fun x -> return x) true
--> return true
```

Hence

$$
M\longrightarrow^*\mathsf{return}\;\mathsf{true}
$$

with pure effect $1$.

## 3. Example B — One operation request

Assume

$$
\mathsf{tell}:\mathsf{String}\to1,
\qquad |\mathsf{tell}|=w.
$$

Consider:

```text
let u <- tell("a") in
return true
```

There is no internal reduction rule for `tell("a")`. Instead, the whole program is already a request form

$$
\mathcal E[\mathsf{tell}(\text{"a"})]
$$

with

```text
E = let u <- [-] in return true
```

The operation itself is just

```text
tell("a")
```

and does not receive `u` or `return true` as arguments.

Its typing is

$$
\mathsf{tell}(\text{"a"}):1!w.
$$

The enclosing `let` has effect

$$
w\cdot1=w.
$$

## 4. Writer machine

Let a Writer configuration be

$$
\langle M,\ell\rangle,
\qquad
\ell\in\mathsf{List}(\mathsf{String}).
$$

Internal reductions lift without changing the log:

$$
\frac{M\longrightarrow M'}
{\langle M,\ell\rangle\longrightarrow_W\langle M',\ell\rangle}.
$$

The Writer response rule is contextual:

$$
\langle\mathcal E[\mathsf{tell}(s)],\ell\rangle
\longrightarrow_W
\langle\mathcal E[\mathsf{return}\;*],
\ell\mathbin{+\!+}[s]\rangle.
\tag{W-Tell}
$$

It appends the message and returns the unit value to the request site.

### Example C — Two ordered writes

```text
let u <- tell("a") in
let v <- tell("b") in
return true
```

Start with an empty log:

```text
< let u <- tell("a") in
  let v <- tell("b") in
  return true,
  [] >
```

The first `W-Tell` replaces the request by `return *`:

```text
-->W
< let u <- return * in
  let v <- tell("b") in
  return true,
  ["a"] >
```

Then `R-Let-Return`:

```text
-->W
< let v <- tell("b") in
  return true,
  ["a"] >
```

The second Writer response:

```text
-->W
< let v <- return * in
  return true,
  ["a", "b"] >
```

Finally:

```text
-->W
< return true,
  ["a", "b"] >
```

Thus the result is `true`, the log is `["a","b"]`, and the effect is

$$
w\cdot w.
$$

## 5. State machine

Use operations

$$
\mathsf{get}:1\to\mathsf{Bool},
\qquad
\mathsf{put}:\mathsf{Bool}\to1
$$

and a Boolean store $s$. The contextual response rules are

$$
\langle\mathcal E[\mathsf{get}(*)],s\rangle
\longrightarrow_S
\langle\mathcal E[\mathsf{return}\;s],s\rangle,
\tag{S-Get}
$$

$$
\langle\mathcal E[\mathsf{put}(s')],s\rangle
\longrightarrow_S
\langle\mathcal E[\mathsf{return}\;*],s'\rangle.
\tag{S-Put}
$$

### Example D — Read, branch, then write

```text
let x <- get(*) in
if x then
  let u <- put(false) in return x
else
  let u <- put(true) in return x
```

Run it from state `true`:

```text
< let x <- get(*) in
  if x then
    let u <- put(false) in return x
  else
    let u <- put(true) in return x,
  true >
```

`S-Get` returns the current state at the request site:

```text
-->S
< let x <- return true in
  if x then
    let u <- put(false) in return x
  else
    let u <- put(true) in return x,
  true >
```

`R-Let-Return` and `R-If-True`:

```text
-->S
< if true then
    let u <- put(false) in return true
  else
    let u <- put(true) in return true,
  true >

-->S
< let u <- put(false) in return true,
  true >
```

`S-Put` supplies unit and changes the state:

```text
-->S
< let u <- return * in return true,
  false >

-->S
< return true, false >
```

The program returns the old bit and flips the stored bit. From initial state `false`, it instead reaches

```text
< return false, true >
```

If $|\mathsf{get}|=r$ and $|\mathsf{put}|=w$, its effect is

$$
r\cdot w.
$$

## 6. Example E — Upper-bound effect

Assume $1\leq w$. Consider:

```text
if false then
  let u <- tell("unreachable") in return true
else
  return false
```

The then branch has effect $w$. The else branch has effect $1$ and can be widened to $w$ by `T-Sub`. Thus the whole computation has effect $w$.

Operationally:

```text
--> return false
```

No Writer request occurs. Hence the current annotation is an upper bound, not an exact claim that `tell` definitely executes.

## 7. Summary

| Example | First observation | Concrete result | Effect |
|---|---|---|---|
| A: pure function | `return true` | — | $1$ |
| B: one request | $\mathcal E[\mathsf{tell}(\text{"a"})]$ | Writer returns unit at the hole | $w$ |
| C: two writes | first contextual `tell` request | value `true`, log `["a","b"]` | $w\cdot w$ |
| D: state flip | contextual `get` request | from `true`: value `true`, state `false` | $r\cdot w$ |
| E: unreachable write | `return false` | empty Writer log | upper bound $w$ |

