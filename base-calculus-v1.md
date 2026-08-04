# Base calculus v1

## Status

**Current Stage 0 working calculus.**

このページだけで、研究の出発点となるbase-effect calculusを固定する。この段階では次のものを導入しない。

- free-operation interface $\Delta$
- free operations
- shallow/deep handlers
- extended effect words
- base effectsとfree effectsのfree product

これらはbase calculusのmetatheoryを確認した後、独立した拡張として一つずつ追加する。

## 1. Design choices

- fine-grain call-by-value
- valuesとcomputationsを構文的に分離
- simply typed、再帰なし
- base operationsはcontinuationを明示したnodeで表す
- base effectsは順序付き逐次合成を持つ
- effect annotationは現段階では安全な上界として読む
- subeffectingのproof自体はprogramから観測できない

## 2. Base effect algebra

Base effectsをpreordered monoid

$$
(B,\cdot,1,\leq)
$$

でindexする。法則は

$$
(b\cdot c)\cdot d=b\cdot(c\cdot d),
\qquad
1\cdot b=b=b\cdot1,
$$

$$
b\leq b',\ c\leq c'
\Longrightarrow
b\cdot c\leq b'\cdot c'
$$

である。積 $b\cdot c$ は「先に $b$、次に $c$」を表し、一般には可換と仮定しない。

Base operation signatureを $\Sigma_B$ とする。各operationはparameter/result typeとprimitive gradeを持つ。

$$
\beta:P_\beta\to R_\beta,
\qquad
|\beta|\in B.
$$

このcalculusは $(B,\Sigma_B,|-|)$ にparameterizedされているが、構文規則と操作的意味論はここで固定する。

## 3. Types and contexts

Value types:

$$
A,B ::= 1
\mid\mathsf{Bool}
\mid\iota
\mid A\times B
\mid A+B
\mid A\to(B!b).
$$

$\iota$ は `String` など、base signatureが必要とするprimitive value typeを表す。

$A\to(B!b)$ は、$A$ の値を受け取り、base effect $b$ を持つ $B$ computationを返すvalue function typeである。

Contextsは

$$
\Gamma=x_1:A_1,\ldots,x_n:A_n
$$

とする。

## 4. Syntax

Values:

$$
\begin{aligned}
V,W ::= {}& x\mid *\mid\mathsf{true}\mid\mathsf{false}
\mid(V,W)\\
&\mid\mathsf{inl}\;V\mid\mathsf{inr}\;V
\mid\lambda x.M.
\end{aligned}
$$

Computations:

$$
\begin{aligned}
M,N ::= {}& \mathsf{return}\;V\\
&\mid\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N\\
&\mid V\,W\\
&\mid\mathsf{if}\;V\;\mathsf{then}\;M\;\mathsf{else}\;N\\
&\mid\mathsf{case}\;V\;\mathsf{of}\;
  \mathsf{inl}\;x\Rightarrow M
  \mid\mathsf{inr}\;y\Rightarrow N\\
&\mid\beta(V;y.M).
\end{aligned}
$$

$\beta(V;y.M)$ はparameter $V$ でbase operationを要求し、そのresultを $y$ としてcontinuation $M$ を実行するexplicit operation nodeである。

## 5. Typing judgments

Value judgmentとcomputation judgmentを

$$
\Gamma\vdash V:A,
\qquad
\Gamma\vdash M:A!b
$$

とする。

Standard rules for variables, unit, booleans, products and sums are assumed. Effect-relevant rulesを明示する。

### Abstraction and application

$$
\frac{\Gamma,x:A\vdash M:B!b}
{\Gamma\vdash\lambda x.M:A\to(B!b)}
\tag{T-Abs}
$$

$$
\frac{
\Gamma\vdash V:A\to(B!b)
\qquad
\Gamma\vdash W:A}
{\Gamma\vdash V\,W:B!b}.
\tag{T-App}
$$

### Return

$$
\frac{\Gamma\vdash V:A}
{\Gamma\vdash\mathsf{return}\;V:A!1}.
\tag{T-Return}
$$

### Sequencing

$$
\frac{
\Gamma\vdash M:A!b
\qquad
\Gamma,x:A\vdash N:C!c}
{\Gamma\vdash
\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N
:C!(b\cdot c)}.
\tag{T-Let}
$$

### Branching

$$
\frac{
\Gamma\vdash V:\mathsf{Bool}
\quad\Gamma\vdash M:A!b
\quad\Gamma\vdash N:A!b}
{\Gamma\vdash
\mathsf{if}\;V\;\mathsf{then}\;M\;\mathsf{else}\;N
:A!b}.
\tag{T-If}
$$

The sum-elimination rule likewise requires both branches to have a common result type and effect $b$. `T-Sub` may first widen them to a common upper bound.

### Base operation

$$
\frac{
\beta:P\to R\in\Sigma_B
\quad\Gamma\vdash V:P
\quad\Gamma,y:R\vdash M:A!b}
{\Gamma\vdash\beta(V;y.M):A!(|\beta|\cdot b)}.
\tag{T-Base-Op}
$$

### Subeffecting

$$
\frac{
\Gamma\vdash M:A!b
\qquad b\leq c}
{\Gamma\vdash M:A!c}.
\tag{T-Sub}
$$

## 6. Operational head forms

Head forms are

$$
Q ::= \mathsf{return}\;V
\mid\beta(V;y.M).
$$

A closed computation either takes an internal step, returns a value, or exposes a base-operation request. The calculus itself does not choose a concrete implementation of $\beta$.

This gives two compatible readings later:

1. $\beta(V;y.M)$ is an observable request in a labelled transition semantics;
2. an external base machine supplies a result $W:R_\beta$ and resumes $M[W/y]$.

The internal reduction relation below is independent of that choice.

## 7. Small-step operational semantics

Computation contexts are

$$
\mathcal E ::= [-]
\mid\mathsf{let}\;x\leftarrow\mathcal E\;\mathsf{in}\;N.
$$

Reduction is closed under these contexts:

$$
\frac{M\longrightarrow M'}
{\mathcal E[M]\longrightarrow\mathcal E[M']}.
\tag{R-Context}
$$

Principal rules are:

$$
(\lambda x.M)\,V\longrightarrow M[V/x],
\tag{R-Beta}
$$

$$
\mathsf{let}\;x\leftarrow\mathsf{return}\;V\;\mathsf{in}\;N
\longrightarrow N[V/x],
\tag{R-Let-Return}
$$

$$
\mathsf{let}\;x\leftarrow\beta(V;y.M)\;\mathsf{in}\;N
\longrightarrow
\beta(V;y.\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N),
\tag{R-Let-Base}
$$

with the usual freshness conditions, and

$$
\mathsf{if}\;\mathsf{true}\;\mathsf{then}\;M\;\mathsf{else}\;N
\longrightarrow M,
\tag{R-If-True}
$$

$$
\mathsf{if}\;\mathsf{false}\;\mathsf{then}\;M\;\mathsf{else}\;N
\longrightarrow N.
\tag{R-If-False}
$$

The standard rules for sum case are analogous. Reduction does not proceed inside the continuation of an exposed operation node $\beta(V;y.M)$ before an operation result is supplied.

## 8. Characteristic calculation

Let

$$
\mathsf{tell}:\mathsf{String}\to1
$$

be a base operation. Then

```text
let x <- tell("a"; u. return true) in
tell("b"; v. return x)
```

reduces by `R-Let-Base` to

```text
tell("a"; u.
  let x <- return true in
  tell("b"; v. return x))
```

and then, inside the suspended continuation once `tell "a"` is resumed, by `R-Let-Return` to

```text
tell("a"; u.
  tell("b"; v. return true))
```

The effect typing records the same order:

$$
|\mathsf{tell}|\cdot|\mathsf{tell}|.
$$

## 9. First metatheory

The Stage 0 proof obligations are:

### B-001 — Value substitution

If $\Gamma,x:A\vdash M:C!b$ and $\Gamma\vdash V:A$, then

$$
\Gamma\vdash M[V/x]:C!b.
$$

### B-002 — Preservation

If

$$
\Gamma\vdash M:A!b
\qquad\text{and}\qquad
M\longrightarrow M',
$$

then

$$
\Gamma\vdash M':A!b.
$$

For `R-Let-Base`, the relevant equality is precisely monoid associativity:

$$
(|\beta|\cdot b)\cdot c
=
|\beta|\cdot(b\cdot c).
$$

### B-003 — Decomposition

A closed well-typed computation is exactly one of:

1. $\mathsf{return}\;V$;
2. $\beta(V;y.M)$;
3. able to take a unique internal reduction step.

### B-004 — Effect soundness interface

Before choosing a concrete base machine, formulate the connection between an exposed $\beta$ and its declared grade $|\beta|$. This will later be the hypothesis required of operational and denotational base models.

## 10. Stage boundary

No free-operation or handler rule may be added to this page. Stage 0 is complete only after:

- the syntax and rules above are accepted;
- B-001--B-003 have paper proofs;
- at least return, sequencing, branching, and two ordered base-operation examples have been calculated;
- the intended reading of base effect annotations as upper bounds has been confirmed or explicitly replaced.

Only then create Stage 1 by adding free operations as a conservative extension.

Worked reductions and concrete Writer/State instantiations are collected in [Base calculus examples v1](base-calculus-examples-v1.md).
