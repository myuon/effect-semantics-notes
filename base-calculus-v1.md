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
- base operationは結果を返す単純なcomputationとして表す
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
&\mid\beta(V).
\end{aligned}
$$

$\beta(V)$ はparameter $V$ でbase operationを要求し、結果型 $R_\beta$ の値を返すcomputationである。operation自身はcontinuationを構文引数に取らない。

後続計算はordinary sequencingで書く。

```text
let y <- beta(V) in M
```

ここでcontinuationに相当するものはoperation termの一部ではなく、外側のevaluation context `let y <- [-] in M` である。

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
\quad\Gamma\vdash V:P}
{\Gamma\vdash\beta(V):R!|\beta|}.
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

Direct head forms are

$$
Q ::= \mathsf{return}\;V
\mid\beta(V).
$$

A base-operation request may occur inside a sequencing context. Thus the observable request forms are

$$
\mathcal E[\beta(V)].
$$

A closed computation either takes an internal step, returns a value, or has this request form. The calculus itself does not choose a concrete implementation of $\beta$.

This gives two compatible readings later:

1. $\mathcal E[\beta(V)]$ is an observable request in a labelled transition semantics;
2. an external base machine supplies a result $W:R_\beta$ by replacing the request with $\mathsf{return}\;W$:

$$
\mathcal E[\beta(V)]
\rightsquigarrow
\mathcal E[\mathsf{return}\;W].
$$

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
\mathsf{if}\;\mathsf{true}\;\mathsf{then}\;M\;\mathsf{else}\;N
\longrightarrow M,
\tag{R-If-True}
$$

$$
\mathsf{if}\;\mathsf{false}\;\mathsf{then}\;M\;\mathsf{else}\;N
\longrightarrow N.
\tag{R-If-False}
$$

The standard rules for sum case are analogous. There is no `R-Let-Base` bubbling rule. A term $\mathcal E[\beta(V)]$ exposes a request together with its surrounding evaluation context; the operation syntax itself contains no continuation.

## 8. Characteristic calculation

Let

$$
\mathsf{tell}:\mathsf{String}\to1
$$

be a base operation. Then

```text
let u <- tell("a") in
let v <- tell("b") in
return true
```

has request form

```text
E[tell("a")]
```

where

```text
E = let u <- [-] in
    let v <- tell("b") in
    return true
```

A Writer machine responds with `return *`; subsequent `R-Let-Return` exposes `tell("b")`. The complete calculation appears in [Base calculus examples v1](base-calculus-examples-v1.md).

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

Internal preservation uses substitution for `R-Beta` and `R-Let-Return`, and common branch effects for conditional/case reduction. Base-machine response steps are treated separately because they discharge an observed operation rather than being internal reductions.

### B-003 — Decomposition

A closed well-typed computation is exactly one of:

1. $\mathsf{return}\;V$;
2. a request form $\mathcal E[\beta(V)]$;
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
