# Finite shallow examples: Writer, State and Exception

## Status

**Worked calculations for Chapter I.**  The examples use the fixed
first-free-boundary matcher: implicit identity return, automatic exactly-once
resumption after a matching response clause, and no reinstallation.

For readability, let

$$
\mathsf{choose}:1\to\mathsf{Bool}
$$

be a new free operation and use the clause

```text
choose() -> return true
```

unless stated otherwise.

## 1. Writer: insertion at the request boundary

Consider

```text
M_W =
  tell("a");
  x <- choose();
  tell(if x then "t" else "f");
  return x
```

Before the free request is exposed, the Writer machine emits `a`.  The residual
context is

```text
x <- [];
tell(if x then "t" else "f");
return x
```

The clause returns `true`, after which the bare context resumes.  Therefore

$$
\mathsf{shallow}_{\mathsf{Choice}}(M_W,h)
\Downarrow_W
([\texttt{a},\texttt{t}],\mathsf{true}).
$$

If the clause itself writes `h`,

```text
choose() -> tell("h"); return true
```

the result is

$$
([\texttt{a},\texttt{h},\texttt{t}],\mathsf{true}).
$$

Thus the handler does not append its base effect globally.  It inserts the
clause computation exactly where the matched request occurred.

## 2. Writer: a second matching operation survives

Let

```text
M_W2 =
  x <- choose();
  y <- choose();
  return (x, y)
```

The first request is replaced by `true`, but its continuation is not rehandled:

```text
shallow_Choice M_W2 with h
-->
y <- choose();
return (true, y)
```

Hence the result still exposes `Choice`.  Both the input and output have the
same safe unordered row

$$
\{\mathsf{Choice}\}.
$$

This is the minimal witness that shallow matching does not generally discharge
an interface from a may-row.

## 3. Writer: a different free request stops the matcher

Let $\mathsf{ask}:1\to\mathsf{Bool}$ belong to another interface.

```text
M_W3 =
  z <- ask();
  x <- choose();
  return x
```

The first free boundary is `ask`, so the Choice matcher forwards it and ends:

```text
shallow_Choice M_W3 with h
-->
z <- ask();
x <- choose();
return x
```

Even if an outer handler later responds to `ask`, the former shallow matcher is
not present to catch `choose`.  This distinguishes the intended construct from
a searching catch and from standard deep forwarding.

## 4. State: the clause runs between prefix and tail

Take integer state with `put` and `get` as old base operations:

```text
M_S =
  put(1);
  x <- choose();
  n <- get();
  return (x, n)
```

With the pure response clause, starting from state $0$ gives

$$
(\mathsf{true},1;\;\text{final state }1).
$$

Now use

```text
choose() -> put(2); return true
```

The prefix `put(1)` has already occurred, the clause changes the state to $2$,
and the bare tail then reads it.  The result is

$$
(\mathsf{true},2;\;\text{final state }2).
$$

This shows why an old State summary cannot in general be transformed without
knowing where the free request lies.  `put(2)` before the tail's `get` is not
equivalent to appending the same state action after the whole computation.

## 5. State: later free operations still survive

```text
M_S2 =
  put(1);
  x <- choose();
  put(3);
  y <- choose();
  n <- get();
  return (x, y, n)
```

After the first response, evaluation reaches

```text
put(3);
y <- choose();
n <- get();
return (true, y, n)
```

so the state becomes $3$ and the second Choice request escapes.  The shallow
matcher has a real state effect but still cannot remove `Choice` from the row.

## 6. Exception: three distinct boundaries

Let `raise` be an old base exception.

First, a base exception before the free request prevents the matcher from ever
reaching it:

```text
raise E;
choose()
```

observes the same exception as the base language.

Second, the response clause may itself raise:

```text
choose() -> raise H
```

In that case the captured tail is never resumed and the result is exception
$H$.

Third, an exception in the bare tail occurs after a successful match:

```text
x <- choose();
raise T
```

reduces through the `true` response and then observes $T$.  These cases show
that the extension preserves the base exception mechanism, but it does not
make an arbitrary handler transparent to old observations.

## 7. Common lesson

Across all three bases, a matching computation factors dynamically as

$$
\text{base prefix} ;\ \text{response clause} ;\ \text{bare tail}.
$$

What differs is the algebra of the old base effect:

- Writer concatenates output in that order;
- State lets the response clause change what the tail reads;
- Exception may abort in any of the three regions.

The unordered free row contains none of this positional information.  It is
sufficient for may-safety, but not for an exact old-effect transformer.
