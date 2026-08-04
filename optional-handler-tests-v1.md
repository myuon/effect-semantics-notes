# Optional handler operational tests v1

## Status

**Exploratory Stage 2 tests; no handler design is adopted yet.**

> **Revision:** The effectful `return` clause and first-class continuation used in P-001--P-010 are deliberately more general than the clarified core syntax. The adopted reconstruction is [Intended shallow matcher v1](intended-shallow-matcher-v1.md), where fallback is identity, the continuation resumes implicitly exactly once, and an unmatched operation is forwarded with no handler reinstallation. This page remains useful as a boundary test for possible future generalizations.

These programs compare:

1. a conventional whole-computation shallow handler that searches through base/mismatching operations;
2. the positional effect order suggested by original Definition 21;
3. an optional-layer eliminator acting at a designated word position.

The calculations assume that effect multiplication is written in operational left-to-right order. If the original thesis uses the opposite convention, the comparison must be reversed.

## 1. Test signature

Let

$$
\mathsf{choose}:1\to\mathsf{Bool}\in\Delta
$$

be the matching free operation.

Use Writer messages as observable base effects:

$$
\mathsf{tell}:\mathsf{String}\to1.
$$

To discuss effect order independently of Writer's coarse grade $w$, write:

- $b$ for a base prefix;
- $e$ for the captured tail effect;
- $e'$ for the handler-clause effect.

The log messages reveal order even when all three are approximated by the same Writer grade.

## 2. Test handler

Use the shallow handler

```text
Hmark = {
  return x ->
    let u <- tell("ret") in
    return x;

  choose(_, k) ->
    let u <- tell("op") in
    k(true);

  otherwise(op, p, k) ->
    forward op(p) and keep handling k
}
```

The matching continuation $k$ is not wrapped again in `Hmark`, so a later `choose` is not automatically handled. The `otherwise` branch uses a different policy: it forwards the mismatching operation but keeps `Hmark` around the resumed continuation so that it can continue searching for a later matching `choose`.

This mixed policy is:

- shallow on a matching operation;
- searching through base and mismatching operations.

## 3. Operational rules used in the tests

### Return

```text
handle_Delta (return V) with Hmark
  -->
let u <- tell("ret") in return V
```

### Matching request

For an active context $\mathcal E$:

```text
handle_Delta E[choose(*)] with Hmark
  -->
let u <- tell("op") in
k(true)
```

where

```text
k = fun x -> E[return x]
```

and `k` is not rehandled.

### Base request

Writer handles an active `tell` while preserving the handler frame:

```text
< handle_Delta E[tell(s)] with Hmark, log >
  -->W
< handle_Delta E[return *] with Hmark,
  log ++ [s] >
```

### Mismatching free request

An operation $\mathsf{ask}_\Gamma$ with $\Gamma\neq\Delta$ is exposed to the outer environment. Under searching forwarding, when the environment supplies $r$, evaluation resumes as

```text
handle_Delta E[return r] with Hmark
```

rather than merely `E[return r]`.

## 4. P-001 — Pure padded return

Program:

```text
handle_Delta (return false : Bool ! Delta) with Hmark
```

The annotation uses $1\leq\Delta$. Operationally:

```text
--> let u <- tell("ret") in return false
-->W return false       log = ["ret"]
```

This agrees with the original no-operation equation: a padded computation selects the value clause.

## 5. P-002 — Padded layer with an effectful tail

Program:

```text
handle_Delta
  (let u <- tell("tail") in
   return false
   : Bool ! Delta . w)
with Hmark
```

The source computation actually has grade $w$ and is widened using

$$
w\leq\Delta\cdot w.
$$

### Conventional operational calculation

The handler searches through the base operation:

```text
< handle_Delta
    (let u <- tell("tail") in return false)
  with Hmark,
  [] >

-->W
< handle_Delta
    (let u <- return * in return false)
  with Hmark,
  ["tail"] >

-->*
< handle_Delta (return false) with Hmark,
  ["tail"] >

-->
< let u <- tell("ret") in return false,
  ["tail"] >

-->W*
< return false,
  ["tail", "ret"] >
```

Thus the operational order is

$$
e\cdot e'.
$$

### Original positional target

Original Definition 21 assigns the handled result grade

$$
e'\cdot e.
$$

Interpreted literally as left-to-right execution, it predicts the order

```text
["ret", "tail"]
```

rather than

```text
["tail", "ret"].
```

Therefore a conventional whole-computation return rule does not validate the original effect order on a padded effectful tail.

## 6. P-003 — Matching operation with a tail

Program:

```text
handle_Delta
  (let x <- choose_Delta(*) in
   let u <- tell("tail") in
   return x)
with Hmark
```

The matching request is exposed before the Writer tail. The handler produces:

```text
let u <- tell("op") in
k(true)
```

with

```text
k = fun x ->
      let u <- tell("tail") in
      return x
```

Since the handler is shallow, `k(true)` runs without reinstalling `Hmark`:

```text
-->W* return true
       log = ["op", "tail"]
```

The order is

$$
e'\cdot e,
$$

which agrees with the original matching-operation target.

Thus the original order works naturally for a real matching operation but not automatically for a padded absence.

## 7. P-004 — Base prefix, matching operation, and tail

Program:

```text
handle_Delta
  (let u <- tell("before") in
   let x <- choose_Delta(*) in
   let v <- tell("tail") in
   return x)
with Hmark
```

The Writer/base prefix is processed while retaining the handler:

```text
log = ["before"]
```

Then `choose` matches, the clause writes `"op"`, and its unhandled continuation writes `"tail"`:

```text
final log = ["before", "op", "tail"]
```

This has order

$$
b\cdot e'\cdot e,
$$

exactly matching the intended positional replacement

$$
b\cdot\Delta\cdot e
\longmapsto
b\cdot e'\cdot e.
$$

## 8. P-005 — Base prefix with a padded absence

Remove `choose` from P-004 but retain the annotation by padding:

```text
handle_Delta
  (let u <- tell("before") in
   let v <- tell("tail") in
   return false
   : Bool ! b . Delta . e)
with Hmark
```

Conventional evaluation produces

```text
["before", "tail", "ret"]
```

with order

$$
b\cdot e\cdot e'.
$$

The original displayed target is

$$
b\cdot e'\cdot e,
$$

corresponding to

```text
["before", "ret", "tail"]
```

Again the disagreement occurs only on the no-operation path with an effectful tail.

## 9. P-006 — Ignoring the shallow continuation

Change the operation clause to

```text
choose(_, k) ->
  let u <- tell("op") in
  return true
```

and reuse P-004. The final log is

```text
["before", "op"]
```

The tail effect $e$ does not execute.

Therefore the fixed output annotation

$$
b\cdot e'\cdot e
$$

is only a safe upper bound if

$$
b\cdot e'
\leq
b\cdot e'\cdot e.
$$

This requires an effect-weakening principle for omission of the tail. It is not automatic in an exact noncommutative monoid.

## 10. P-007 — Duplicating the shallow continuation

Change the operation clause to invoke $k$ twice:

```text
choose(_, k) ->
  let u <- tell("op") in
  let x <- k(true) in
  k(false)
```

For a continuation that writes `"tail"`, the log is

```text
["op", "tail", "tail"]
```

The operational effect is

$$
e'\cdot e\cdot e.
$$

The original fixed target $e'\cdot e$ is sound only if at least one of the following holds:

1. continuation variables are affine/linear and cannot be duplicated;
2. tail effects are idempotent or satisfy $e\cdot e\leq e$;
3. the clause type records continuation usage multiplicity;
4. the handler output effect is inferred from the clause body rather than fixed in advance.

This issue is independent of optional padding and must be resolved for shallow handlers generally.

## 11. P-008 — Two matching operations

Program:

```text
handle_Delta
  (let x <- choose_Delta(*) in
   let y <- choose_Delta(*) in
   return y)
with Hmark
```

The first `choose` matches. Its continuation is

```text
k = fun x ->
      let y <- choose_Delta(*) in
      return y
```

The clause writes `"op"` and invokes `k(true)` without reinstalling the handler. The second `choose` is therefore exposed unhandled:

```text
log = ["op"]
next observation = choose_Delta(*)
```

This is the characteristic shallow behavior.

## 12. P-009 — Mismatching operation before a match

Let

$$
\mathsf{ask}:1\to\mathsf{Bool}\in\Gamma,
\qquad\Gamma\neq\Delta.
$$

Program:

```text
handle_Delta
  (let z <- ask_Gamma(*) in
   let x <- choose_Delta(*) in
   return x)
with Hmark
```

### Forward and stop searching

The outer environment first sees `ask`. If its continuation is resumed without `Hmark`, the later `choose` is also exposed unhandled.

### Forward and keep searching

The outer environment sees `ask`, but its resumed continuation is

```text
handle_Delta
  (let x <- choose_Delta(*) in return x)
with Hmark
```

The later `choose` is then matched and handled.

These behaviors are observably different. An `otherwise` clause that means “pass through and continue handling” selects the second policy.

## 13. P-010 — Padding position and handler style

Widen a one-operation computation from $\Delta$ to $\Delta\Delta$.

Semantically there are two layer embeddings:

```text
skip; op
```

and

```text
op; skip
```

### Positional one-layer eliminator

A handler targeting the first annotated layer distinguishes them:

- `skip; op`: it eliminates an absent first layer and leaves the actual operation in the tail;
- `op; skip`: it handles the actual operation immediately.

Therefore padding evidence must be proof-relevant or canonically elaborated.

### Search-for-next-match handler

A handler that ignores silent padding and searches for the next actual $\Delta$ request handles the same operation in both cases. For this handler style, padding positions may be observationally irrelevant and a proof-irrelevant quotient becomes plausible.

Thus the padding-coherence problem is coupled to the handler philosophy:

$$
\boxed{
\text{positional layer handler}
\Rightarrow
\text{padding position observable}
}
$$

$$
\boxed{
\text{searching handler}
\Rightarrow
\text{padding may be erasable}
}
$$

## 14. Comparison table

| Situation | Conventional searching shallow handler | Original positional equation |
|---|---|---|
| pure padded return | value clause | value lifting |
| matching op + tail | clause, then tail: $e'e$ | $e'e$ |
| base + matching op + tail | $be'e$ | $be'e$ |
| padded absence + effectful tail | tail, then return clause: $ee'$ | $e'e$ |
| ignored continuation | tail omitted | fixed target includes $e$ unless weakened |
| duplicated continuation | tail repeated | fixed target needs usage/idempotence |
| mismatching operation | policy-dependent forwarding | not specified in excerpt |
| repeated padding | invisible to searching handler | visible to positional eliminator |

## 15. Main diagnosis

There are two coherent but different language philosophies.

### A. Conventional searching shallow handler

- effects are upper bounds;
- $1\leq\Delta$ is proof-irrelevant or canonically elaborated;
- silent padding has no runtime position;
- base and mismatching operations are forwarded while search continues;
- return clause runs after the handled computation actually returns;
- no-operation effect order is $be e'$;
- matching-operation effect order is $be'e$.

The output effect depends on whether a match occurs, so a common upper bound or effect join is needed.

### B. Positional optional-layer eliminator

- $b\Delta e$ denotes a designated boundary;
- padding inserts a real silent boundary at a position;
- handler eliminates that boundary locally;
- both skip and operation branches replace the boundary by $e'$;
- output order is uniformly $be'e$;
- padding position is observable, so proof relevance/canonical insertion is required;
- the value lifting $T_{be}A\to T_{be'e}C$ needs additional semantic structure and may not have a causal operational implementation for arbitrary effects.

Original Definition 21 is closer to B. The user-facing `otherwise` intuition is closer to A.

## 16. Recommended next decision

Do not choose based only on carrier elegance. Choose which of these two programs should be the intended behavior:

```text
handle_Delta
  (tell("tail"); return false : Bool ! Delta . w)
with {
  return x -> tell("ret"); return x
  ...
}
```

Should the observable log be

```text
["tail", "ret"]
```

or

```text
["ret", "tail"]
```

The first selects a conventional whole-computation handler. The second selects the original positional layer-replacement philosophy and requires the calculus to expose/suspend the tail boundary explicitly.
