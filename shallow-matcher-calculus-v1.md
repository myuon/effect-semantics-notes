# Shallow matcher calculus v1

## Status

**Adopted Stage 2 operational calculus and exhaustive-interface typing.**

This page extends the fixed Stage 0 calculus with simple free operations and the
one-shot shallow matcher. It fixes the source syntax, call-by-value control flow,
and principal reduction rules. A handler indexed by $\Delta$ must contain a
branch for every operation declared in $\Delta$. The remaining open design
choice concerns only the representation and coherence of subeffect evidence.

## 1. Parameters

Keep the Stage 0 base signature and preordered monoid

$$
(B,\cdot,1,\leq_B).
$$

Let $\mathcal D$ be a collection of free-operation interfaces. Each
$\Delta\in\mathcal D$ consists of declarations

$$
\operatorname{op}:P_{\operatorname{op}}\to R_{\operatorname{op}}.
$$

Operation names are assumed globally qualified by their interface. Thus
$\operatorname{op}_\Delta$ and $\operatorname{op}_\Gamma$ are distinct when
$\Delta\neq\Gamma$.

## 2. Syntax

Stage 0 values are unchanged. Extend computations by

$$
\begin{aligned}
M,N ::= {}& \cdots
\mid \operatorname{op}_\Delta(V)\\
&\mid \mathsf{handle}_\Delta\;M\;\mathsf{with}\;H,
\end{aligned}
$$

where a handler for $\Delta$ has exactly one typed clause for every operation
declared in $\Delta$

$$
H_\Delta::=\{\operatorname{op}_i(x_i)\Rightarrow M_i\}_{\operatorname{op}_i\in\Delta}
\quad[;\ \_\Rightarrow y].
$$

Clause names must be distinct. Omitting any operation in $\Delta$ or adding a
clause from another interface is ill formed.

The final clause is optional notation for the fixed identity fallback. It covers
returned values and requests from interfaces other than $\Delta$; it is not an
arbitrary computation and binds no continuation. In particular, the following
core language has no continuation variable $k$.

For readability, a singleton handler is written

```text
handle_Delta M with {
  op(x) -> N;
  _     -> y
}
```

## 3. Evaluation contexts and observable heads

The sequencing contexts captured with a free request are

$$
\mathcal E::=[-]
\mid
\mathsf{let}\;x\leftarrow\mathcal E\;\mathsf{in}\;N.
$$

The handler itself is an evaluation context only while its scrutinee is taking
ordinary internal steps:

$$
\mathcal F::=\mathcal E
\mid \mathsf{handle}_\Delta\;\mathcal F\;\mathsf{with}\;H.
$$

This grammar does **not** mean that a handler is captured into the continuation
of a free request. The principal handler rules below take precedence exactly
when the scrutinee has reached its first observable free head.

The relevant head outcomes are

$$
\mathsf{return}\;V,
\qquad
\mathcal E[\beta(V)],
\qquad
\mathcal E[\operatorname{op}_\Gamma(V)].
$$

A base request $\beta(V)$ is serviced by the chosen base machine while the
matcher remains pending. A free request is the event inspected by the matcher.

## 4. Internal call-by-value rules

All Stage 0 principal rules are retained. Closure under sequencing is retained:

$$
\frac{M\longrightarrow M'}
{\mathcal E[M]\longrightarrow\mathcal E[M']}.
\tag{R-Seq-Ctx}
$$

The handler evaluates its scrutinee:

$$
\frac{M\longrightarrow M'}
{\mathsf{handle}_\Delta\;M\;\mathsf{with}\;H
 \longrightarrow
 \mathsf{handle}_\Delta\;M'\;\mathsf{with}\;H}.
\tag{R-Handle-Ctx}
$$

This is ordinary CBV evaluation, not recursive handler installation.

## 5. The three terminal handler rules

### 5.1 Returned value

$$
\mathsf{handle}_\Delta\;(\mathsf{return}\;V)\;\mathsf{with}\;H
\longrightarrow
\mathsf{return}\;V.
\tag{R-Handle-Return}
$$

The identity fallback performs no runtime effect.

### 5.2 Matching free request

Suppose $H$ contains
$\operatorname{op}(x)\Rightarrow N$ and
$\operatorname{op}:P\to R\in\Delta$. Then

$$
\mathsf{handle}_\Delta\;
  \mathcal E[\operatorname{op}_\Delta(V)]
\;\mathsf{with}\;H
\longrightarrow
\mathsf{let}\;r\leftarrow N[V/x]\;\mathsf{in}\;
  \mathcal E[\mathsf{return}\;r].
\tag{R-Handle-Match}
$$

Here $r:R$. The branch computes the replacement result of the operation. The
captured sequencing context $\mathcal E$ is then resumed exactly once. The
right-hand side contains no occurrence of the matcher.

### 5.3 Unmatched free request

If the exposed qualified operation has no matching clause in $H$, then

$$
\mathsf{handle}_\Delta\;
  \mathcal E[\operatorname{op}_\Gamma(V)]
\;\mathsf{with}\;H
\xRightarrow{\operatorname{op}_\Gamma(V)}
\mathcal E[-].
\tag{R-Handle-Forward}
$$

This is a labelled request transition: the outside world receives the request
together with residual continuation $\mathcal E[-]$. If it answers with
$W:R_{\operatorname{op}}$, execution continues as

$$
\mathcal E[\mathsf{return}\;W].
$$

It does **not** continue as

$$
\mathsf{handle}_\Delta\;
  \mathcal E[\mathsf{return}\;W]\;\mathsf{with}\;H.
$$

Therefore forwarding ends the handler. A later matching operation in
$\mathcal E$ remains unhandled.

## 6. Base-machine interaction

The direct rule below is the single-handler instance of the compositional
labelled semantics in
[Stage 2 operational metatheory v1](stage2-operational-metatheory-v1.md). In
particular, nested handlers distinguish base propagation (retain the pending
handler) from unmatched free propagation (remove it).

Base requests are not candidates for free-operation matching. If the base
machine responds to

$$
\mathcal E[\beta(V)]
$$

with $W:R_\beta$, then a pending handler evolves by

$$
\mathsf{handle}_\Delta\;
  \mathcal E[\beta(V)]\;\mathsf{with}\;H
\rightsquigarrow_B
\mathsf{handle}_\Delta\;
  \mathcal E[\mathsf{return}\;W]\;\mathsf{with}\;H.
\tag{M-Handle-Base}
$$

Thus base effects occurring before the first free request are executed in CBV
order, and the matcher continues waiting. This rule belongs to the combined
machine semantics, not to pure internal reduction.

## 7. Free-operation typing

Let extended effects form a noncommutative monoidal upper-bound structure
$\widehat B$ containing $B$ and the interface tokens. Sequential composition is
written by juxtaposition or $\cdot$. Assume

$$
1\leq\Delta
\qquad(\Delta\in\mathcal D)
$$

and monotonicity of composition. The primitive rule is

$$
\frac{
\operatorname{op}:P\to R\in\Delta
\qquad
\Gamma\vdash V:P
}{
\Gamma\vdash\operatorname{op}_\Delta(V):R!\Delta
}.
\tag{T-Free-Op}
$$

Stage 0 `T-Let` and `T-Sub` are reused over $\widehat B$.

At the surface level, $1\leq\Delta$ means “may perform a $\Delta$ operation.”
It has no dynamic reduction rule. A semantics must implement it either by
proof-relevant padding, canonical elaboration, or a proof-irrelevant trace-bound
model.

## 8. Core handler typing

The word-elimination rule below relies on the well-formedness requirement that
the handler covers every operation represented by the selected $\Delta$ token.
The complete preservation derivation is in
[Residual context typing v1](residual-context-typing-v1.md).

Define the handler-clause judgment

$$
\Gamma\vdash H:\Delta\Rightarrow e'
$$

by

$$
\frac{
\operatorname{dom}(H)=\operatorname{ops}(\Delta)
\qquad
\forall(\operatorname{op}_i:P_i\to R_i\in\Delta).\;
\Gamma,x_i:P_i\vdash H(\operatorname{op}_i):R_i!e'
}{
\Gamma\vdash H:\Delta\Rightarrow e'
}.
\tag{T-Handler-WF}
$$

Equality of domains enforces both coverage and absence of duplicate/foreign
clauses. Suppose the scrutinee has the upper-bound shape

$$
b\cdot\Delta\cdot e
$$

and the matching branch has effect $e'$:

$$
\frac{
\Gamma\vdash M:A!(b\Delta e)
\qquad
\Gamma\vdash H:\Delta\Rightarrow e'
\qquad
1\leq e'
}{
\Gamma\vdash
\mathsf{handle}_\Delta\;M\;\mathsf{with}\;H
:A!(b e' e)
}.
\tag{T-Handle}
$$

Every clause body must have the corresponding operation result type and a common
effect upper bound $e'$. Partial handlers are not terms of the core calculus.

This rule records the order of the matching execution:

$$
\underbrace{b}_{\text{prefix}}
\cdot
\underbrace{e'}_{\text{branch}}
\cdot
\underbrace{e}_{\text{resumed tail}}.
$$

On return or unmatched paths the branch does not execute. Their actual bound is
$b e$, which widens to the declared result because

$$
b e=b1e\leq be'e
$$

provided $1\leq e'$. This is the final premise of `T-Handle`:

$$
1\leq e'.
\tag{Optional-Branch}
$$

It is automatic if every primitive effect token may be inserted and the order
is closed under sequential composition. If the language later admits mandatory
effects, `T-Handle-1` must retain this premise rather than assume it globally.

## 9. Preservation calculations

### Matching case

By inversion of the scrutinee typing at its exposed request, the captured
context accepts an $R$ result and contributes tail effect $e$. Substitution gives

$$
\Gamma\vdash N[V/x]:R!e'.
$$

Therefore

$$
\Gamma\vdash
\mathsf{let}\;r\leftarrow N[V/x]\;\mathsf{in}\;
\mathcal E[\mathsf{return}\;r]
:A!(e'e)
$$

after the already executed prefix $b$. This is exactly $be'e$.

### Return case

The reduct has the original value type and pure dynamic effect. The effects
already performed while evaluating the scrutinee form a prefix bounded by
$be$; `Optional-Branch` widens this to $be'e$.

### Forward case

Forwarding preserves the operation request and its residual continuation; it
only removes the matcher. The emitted request therefore has the same parameter,
result type, and continuation result type as before. Its trace is bounded by the
no-match bound $be\leq be'e$.

The residual-effect inversion lemma and the resulting local preservation theorem
are proved in [Residual context typing v1](residual-context-typing-v1.md). They
also show why forwarding from a partial handler cannot erase the unmatched
operation token.

## 10. Determinism and one-shot decomposition

For a closed, well-typed handler configuration, exactly one of the following
applies:

1. its scrutinee takes a unique internal step;
2. the base machine sees a unique base request and may respond;
3. `R-Handle-Return` applies;
4. exactly one qualified clause matches and `R-Handle-Match` applies;
5. no clause matches and `R-Handle-Forward` applies.

This is deterministic relative to a deterministic base machine. Clause names
must be unique, and `R-Handle-Ctx` must not step across an observable request.

In cases 3--5 the handler disappears. This is the formal one-shot shallowness
invariant.

## 11. Sanity calculations

Let `choose : 1 -> Bool` belong to $\Delta$ and `ask : 1 -> Bool` belong to
$\Gamma\neq\Delta$.

### Matching first request

```text
handle_Delta
  (let x <- choose_Delta(*) in
   let u <- tell("tail") in
   return x)
with { choose(_) -> return true }
```

reduces to

```text
let r <- return true in
let x <- return r in
let u <- tell("tail") in
return x
```

and then writes `"tail"` and returns `true`. No handler surrounds the tail.

### Unmatched first request

```text
handle_Delta
  (let z <- ask_Gamma(*) in
   let x <- choose_Delta(*) in
   return x)
with { choose(_) -> return true }
```

forwards `ask_Gamma(*)` with continuation

```text
let z <- [-] in
let x <- choose_Delta(*) in
return x
```

and removes the handler. After an answer to `ask`, the later `choose` is exposed
to the outside world and is not handled.

### Base request before a free request

```text
handle_Delta
  (let u <- tell("before") in
   choose_Delta(*))
with { choose(_) -> return true }
```

first lets the Writer machine service `tell("before")` while retaining the
handler. It then matches `choose` and returns `true`.

## 12. Metatheoretic obligations

The next proofs should be attempted in this order:

1. typed evaluation-context decomposition with residual effects;
2. substitution for handler branches;
3. internal preservation for `R-Handle-Match` and `R-Handle-Return`;
4. typed labelled preservation for `R-Handle-Forward`;
5. deterministic decomposition relative to a base machine;
6. trace-bound soundness of $1\leq\Delta$;
7. coherence or proof relevance of repeated padding;
8. denotational interpretation of `T-Handle-1`.

Items 1--5 depend only weakly on the eventual padding representation. Items
6--8 are where the proof-relevant-layer and trace-bound semantics genuinely
diverge.
