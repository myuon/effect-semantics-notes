# Intended shallow matcher v1

## Status

**Adopted reconstruction of the intended core handler behavior.**

This page supersedes the assumption that the source handler has an arbitrary effectful return clause and an explicitly user-controlled continuation. The intended construct is instead a one-shot operation matcher with an implicit identity fallback.

## 1. Surface syntax

For an operation

$$
\operatorname{op}:P\to R,
$$

the intended syntax is schematically

```text
handle e with {
  op(x) -> M;
  _     -> y
}
```

where the final identity branch may be omitted:

```text
handle e with {
  op(x) -> M
}
```

The matching branch supplies a replacement result for the operation. Thus its body has the operation result type:

$$
\Gamma,x:P\vdash M:R!e'.
$$

There is no source variable $k$ for the continuation in this core syntax.

## 2. Evaluation before matching

The scrutinee $e$ is evaluated until it reaches one of the observable head outcomes:

1. a returned value $\mathsf{return}\;V$;
2. a free request $\mathcal E[\operatorname{op}_\Gamma(t)]$.

Base operations are executed/forwarded by the selected base machine during this search.

The evaluation context $\mathcal E$ is the residual continuation, but it is metatheoretic rather than a syntactic argument of the operation or handler clause.

## 3. Matching rule

For a matching operation:

```text
handle_Delta E[op_Delta(t)] with {
  op_Delta(x) -> M;
  _ -> y
}
```

reduce to

```text
let r <- M[t/x] in
E[return r]
```

where $r:R$.

Thus the residual continuation is:

- captured automatically;
- resumed exactly once;
- resumed after the branch body;
- not wrapped again in the same handler.

This explains the shallow behavior without exposing a first-class continuation variable.

If

$$
\Gamma,x:P\vdash M:R!e'
$$

and the captured tail has effect $e$, the actual matching-path order is

$$
e'\cdot e.
$$

With a base prefix $b$, it is

$$
b\cdot e'\cdot e.
$$

This matches the original displayed handler target.

## 4. Value fallback

If the scrutinee returns a value:

```text
handle_Delta (return V) with {
  op_Delta(x) -> M;
  _ -> y
}
```

the implicit identity fallback gives

```text
--> return V
```

There is no arbitrary user-specified return computation and no additional runtime effect.

For an effectful no-match path such as

```text
handle_Delta
  (let u <- tell("tail") in return false)
with { choose(x) -> M }
```

the Writer outcome is therefore

```text
log = ["tail"]
value = false
```

not `["tail","ret"]` and not `["ret","tail"]`.

## 5. Why a uniform output $be'e$ can still type

Suppose the handler branch has effect upper bound $e'$. On the matching path, execution genuinely has order

$$
b\cdot e'\cdot e.
$$

On the value/no-match path, execution has only

$$
b\cdot e.
$$

If effects always admit optional insertion,

$$
1\leq e',
$$

monotonicity gives

$$
b\cdot e
=b\cdot1\cdot e
\leq
b\cdot e'\cdot e.
$$

Therefore both paths can receive the common upper-bound output

$$
b\cdot e'\cdot e.
$$

The inserted $e'$ on the no-match path is static padding; it does not mean that the operation branch executed.

This supplies a plausible operational explanation for the original uniform target without requiring an effectful return clause to run before the tail.

## 6. Re-reading the original value equation

The equation

$$
H_\Delta
\circ
\widehat T_{be\leq b\Delta e}
=
(c_{\mathsf{val}})^\sharp
$$

should first be instantiated with the identity value behavior

$$
c_{\mathsf{val}}(x)=\mathsf{return}\;x.
$$

Then $(c_{\mathsf{val}})^\sharp$ may be read as:

1. preserve the already evaluated no-match result;
2. insert the handler-branch effect upper bound $e'$ at the removed $\Delta$ position;
3. perform no runtime branch effect.

The original definition generalized $c_{\mathsf{val}}$ to an arbitrary effectful map. That generalization remains suspect: a genuinely effectful value clause would execute after the tail under ordinary CBV and therefore have order $bee'$, not $be'e$.

Thus the core language can be sound even if the original abstract $c_{\mathsf{val}}$ interface was overgeneralized.

## 7. Mismatching operation fallback

For $\Gamma\neq\Delta$, the implicit identity fallback most directly means:

```text
handle_Delta E[op_Gamma(t)] with H
```

exposes/forwards the same unmatched request and removes the handler. After the outer environment supplies a result, evaluation resumes as

```text
E[return r]
```

not

```text
handle_Delta E[return r] with H.
```

Therefore the adopted rule is **forward and stop searching**. A later matching $\Delta$ in the unmatched continuation is not handled automatically.

There is no “forward and reinstall” behavior in the core calculus. Such a construct would be a separate recursive/searching handler and would not have the intended shallowness.

## 7.1 One-shot head observation

The complete control-flow principle is:

> Evaluate the scrutinee $e$ by call-by-value until its first observable head outcome, inspect that outcome exactly once, and then remove the handler permanently.

The three outcomes are:

$$
\begin{array}{rcl}
\mathsf{return}\;V
&\mapsto&
\mathsf{return}\;V,\\[1mm]
\mathcal E[\operatorname{op}_\Delta(t)]
&\mapsto&
\mathsf{let}\;r\leftarrow M[t/x]\;\mathsf{in}\;
\mathcal E[\mathsf{return}\;r],\\[1mm]
\mathcal E[\operatorname{op}_\Gamma(t)]\quad(\Gamma\neq\Delta)
&\mapsto&
\text{forward }\mathcal E[\operatorname{op}_\Gamma(t)].
\end{array}
$$

In every row, the reduct/forwarded continuation contains no occurrence of the eliminated handler.

## 8. Continuation usage is fixed

Because the matching clause has no $k$, the core construct cannot:

- ignore the captured continuation;
- invoke it twice;
- store it;
- resume it under the same handler.

It always resumes exactly once after producing the operation result.

Therefore the earlier continuation-usage problem disappears for this syntax. The tail effect $e$ occurs exactly once on the matching path, justifying $e'\cdot e$ without linear types or idempotence assumptions.

First-class $k$ may later be added as a genuine extension, but then its usage must be reflected in the effect system.

## 9. Revised operational tests

Let

```text
Hchoose = {
  choose(_) ->
    let u <- tell("op") in
    return true
}
```

### No operation

```text
handle_Delta
  (let u <- tell("tail") in return false)
with Hchoose
```

evaluates to

```text
return false
log = ["tail"]
```

and is typed at the upper bound $e'e$ by padding $e'$.

### One matching operation

```text
handle_Delta
  (let x <- choose(*) in
   let u <- tell("tail") in
   return x)
with Hchoose
```

evaluates in the order

```text
branch writes "op"
branch returns true
captured continuation resumes
tail writes "tail"
return true
```

so

```text
log = ["op", "tail"]
```

### Two matching operations

```text
handle_Delta
  (let x <- choose(*) in
   let y <- choose(*) in
   return y)
with Hchoose
```

handles the first request, resumes its continuation without the handler, and leaves the second `choose` exposed. This remains shallow.

### Mismatching operation first

```text
handle_Delta
  (let z <- ask_Gamma(*) in
   let x <- choose_Delta(*) in
   return x)
with Hchoose
```

under identity fallback forwards `ask` and removes the handler, so the later `choose` is also unhandled.

## 10. Consequence for padding coherence

If silent padding is erased operationally and the handler only reacts to the first actual matching request, the two embeddings

```text
skip; op
```

and

```text
op; skip
```

produce the same core runtime behavior under this matcher.

This makes proof-irrelevant padding more plausible than it was for a positional one-layer eliminator. However, denotational layer models that retain explicit skip positions must then quotient those positions or prove that all handler observations ignore them.

Thus there are two semantic presentations to compare:

1. proof-relevant padded layers, followed by an observational quotient;
2. directly define computations as operation trees whose traces are bounded by effect words, with padding absent from runtime data.

The second is likely closer to the intended surface language.

## 11. Current reconstructed philosophy

The intended core appears to be:

- effect annotations are ordered upper bounds;
- $1\leq\Delta$ is allowed;
- operation syntax does not contain a continuation;
- handler evaluates to a value or active operation request;
- a matching branch replaces the operation result;
- the captured continuation resumes automatically exactly once;
- matching continuation is not rehandled, hence shallow;
- value and unmatched cases use an implicit identity fallback and terminate the handler;
- the branch effect is inserted as a static upper bound on paths where the branch does not execute.

This is neither a fully general algebraic handler nor a positional skip-layer eliminator. It is a selective, one-shot shallow operation matcher.
