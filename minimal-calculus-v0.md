# Minimal calculus v0

> **Superseded for forward development.** 探索過程として保存する。現在の working definition は [Baseline calculus v1](baseline-calculus-v1.md)。

## 目的

この calculus は最終案ではない。次の二つを混同せず比較するための基準面である。

1. 標準的な shallow handler の操作的振る舞い
2. base effects と free-effect interfaces の交互列による精密な effect annotation

まず 1 を固定する。2 は後から annotation/refinement として載せ、載らない場合は意味論候補を修正する。

## 0. Scope

最初の版では以下に限定する。

- fine-grain call-by-value
- value/computation の構文的分離
- 単純型、関数、algebraic operations
- explicit operation node と continuation
- shallow handlers
- recursion、effect polymorphism、dynamic instances はなし
- base effects は抽象的な graded monad に委ね、具体的な base-operation syntax は後で追加

## 1. Signatures and types

Free-effect interface $\Delta$ は operation symbols の族である。

$$
\operatorname{op}\in\Delta
\qquad
\operatorname{op}:P_{\operatorname{op}}\to R_{\operatorname{op}}.
$$

値型の最小 grammar を

$$
A,B ::= 1 \mid A\times B \mid A\to (B\,\mathsf{comp})
$$

と置く。関数型に effect annotation を入れるのは effect algebra を固定した後に行う。

## 2. Syntax

Values:

$$
V,W ::= x \mid * \mid (V,W) \mid \lambda x.M
$$

Computations:

$$
M,N ::= \mathsf{return}\;V
\mid \mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N
\mid V\,W
\mid \operatorname{op}(V;y.M)
\mid \mathsf{handle}^{\mathsf{sh}} M\;\mathsf{with}\;H.
$$

$\operatorname{op}(V;y.M)$ は parameter $V$ で operation を発生させ、result を $y$ として continuation $M$ を実行する明示的 operation node である。

A handler は

$$
H=
\{\mathsf{return}\;x\mapsto M_r;\;
  \operatorname{op}(p;k)\mapsto M_{\operatorname{op}}\}_{\operatorname{op}\in\Delta}
$$

とする。

## 3. Unannotated typing skeleton

ここでは effect annotation をまだ入れず、handler の変数束縛だけを確定する。

$$
\frac{\Gamma\vdash V:A}
     {\Gamma\vdash \mathsf{return}\;V:A\;\mathsf{comp}}
$$

$$
\frac{\Gamma\vdash M:A\;\mathsf{comp}
\qquad
\Gamma,x:A\vdash N:B\;\mathsf{comp}}
{\Gamma\vdash \mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N:B\;\mathsf{comp}}
$$

$$
\frac{
 \operatorname{op}:P\to R\in\Delta
 \qquad \Gamma\vdash V:P
 \qquad \Gamma,y:R\vdash M:A\;\mathsf{comp}}
{\Gamma\vdash \operatorname{op}(V;y.M):A\;\mathsf{comp}}
$$

For a handler from result type $A$ to $C$:

$$
\Gamma,x:A\vdash M_r:C\;\mathsf{comp}
$$

and, for every $\operatorname{op}:P\to R\in\Delta$,

$$
\Gamma,p:P,k:(R\to A\;\mathsf{comp})
\vdash M_{\operatorname{op}}:C\;\mathsf{comp}.
$$

The continuation variable $k$ returns a computation of the original result type $A$. The defining shallow/deep distinction is how this continuation is constructed by reduction.

## 4. Operational semantics

The two characteristic shallow-handler reductions are:

$$
\mathsf{handle}^{\mathsf{sh}}(\mathsf{return}\;V)\;\mathsf{with}\;H
\longrightarrow
M_r[V/x]
$$

and

$$
\mathsf{handle}^{\mathsf{sh}}(\operatorname{op}(V;y.M))\;\mathsf{with}\;H
\longrightarrow
M_{\operatorname{op}}
[V/p,(\lambda y.M)/k].
$$

The crucial point is the operation rule:

$$
k=\lambda y.M,
$$

not

$$
k=\lambda y.\mathsf{handle}^{\mathsf{sh}}M\;\mathsf{with}\;H.
$$

The latter would be the characteristic deep-handler continuation.

For a surface term `perform op V`, an evaluation context can elaborate it into an explicit node

$$
\operatorname{op}(V;y.E[\mathsf{return}\;y]).
$$

Using explicit nodes avoids hiding the captured continuation in the metatheory.

## 5. First effect annotation candidate

Let $E$ be an effect algebra with sequential product $\cdot$, unit effect $1$, and preorder $\leq$. Use judgments

$$
\Gamma\vdash M:A\;!\;e.
$$

The unsurprising rules are:

$$
\frac{\Gamma\vdash V:A}
{\Gamma\vdash\mathsf{return}\;V:A!1}
$$

$$
\frac{\Gamma\vdash M:A!e\qquad\Gamma,x:A\vdash N:B!f}
{\Gamma\vdash\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N:B!(e\cdot f)}
$$

$$
\frac{\Gamma\vdash M:A!e\qquad e\leq f}
{\Gamma\vdash M:A!f}.
$$

For an operation node, the first simple candidate is

$$
\frac{
 \operatorname{op}:P\to R\in\Delta
 \quad \Gamma\vdash V:P
 \quad \Gamma,y:R\vdash M:A!e}
{\Gamma\vdash\operatorname{op}(V;y.M):A!(\Delta\cdot e)}.
$$

This records that the operation occurs before its continuation.

## 6. Handler effect rule: provisional form

Assume

$$
\Gamma\vdash M:A!(\Delta\cdot e).
$$

The continuation handed to an operation clause has type

$$
k:R\to(A!e),
$$

because shallow handling does not eliminate $\Delta$ occurrences in the continuation.

A provisional handler rule is:

$$
\frac{
\Gamma\vdash M:A!(\Delta\cdot e)
\quad
\Gamma,x:A\vdash M_r:C!f
\quad
\forall\operatorname{op}:P\to R\in\Delta.\;
\Gamma,p:P,k:R\to(A!e)\vdash M_{\operatorname{op}}:C!f
}
{
\Gamma\vdash\mathsf{handle}^{\mathsf{sh}}M\;\mathsf{with}\;H:C!f
}.
$$

This deliberately uses a common output effect $f$ for all clauses. It is simple but may be too coarse: an operation clause invoking $k$ must account for the tail effect $e$, and different clauses may use the continuation differently. A more precise rule may grade handler clauses by an effect expression containing $e$.

## 7. Conflict discovered with Candidate A

The earlier semantic candidate used

$$
\widehat T_{b\Delta e}X
=
T_b\left(
\widehat T_eX +
\coprod_i A_i\times(B_i\Rightarrow\widehat T_eX)
\right).
$$

Its left branch contains an entire tail computation $\widehat T_eX$, whereas the standard shallow return rule supplies a value $X$ to the return clause.

These express different decompositions:

- **Head-normal decomposition:** either the computation returns $X$, or exposes one operation with a residual continuation.
- **Word-layer decomposition:** at a designated $\Delta$-boundary, either skip that layer and run a tail computation, or expose an operation from that layer.

Therefore Candidate A is not yet a semantics of the standard calculus above. At least one of the following must be true:

1. the original system has a nonstandard layer handler whose value clause consumes a tail computation;
2. the left branch should be $X$, with recursion/fixed points used to represent later effects;
3. $\widehat T_eX$ is suspended syntax and the handler rule must explicitly describe how it is resumed;
4. effect words classify semantic layers rather than direct operational traces.

This is the first major design fork. It must be resolved before proving graded monad laws.

## 8. Test programs

Let $\operatorname{ask}:1\to\mathsf{Bool}\in\Delta$.

### T-001: return

$$
\mathsf{handle}^{\mathsf{sh}}(\mathsf{return}\;\mathsf{true})\;\mathsf{with}\;H
$$

must select the return clause.

### T-002: one operation

$$
\mathsf{handle}^{\mathsf{sh}}
(\operatorname{ask}(*;b.\mathsf{return}\;b))
\;\mathsf{with}\;H
$$

must pass $\lambda b.\mathsf{return}\;b$ unhandled to the `ask` clause.

### T-003: two operations

$$
\mathsf{handle}^{\mathsf{sh}}
(\operatorname{ask}(*;b_1.\operatorname{ask}(*;b_2.\mathsf{return}(b_1,b_2))))
\;\mathsf{with}\;H.
$$

Only the first `ask` is handled automatically. If the clause invokes $k$, the second `ask` remains unhandled by the same handler.

### T-004: ignored continuation

An operation clause may ignore $k$. The effect rule should then avoid charging the continuation effect $e$, if the system aims to track effects precisely. This exposes why the provisional common-output rule is coarse.

## 9. Immediate next calculations

1. Reconstruct the original handler typing rule and compare it with Section 6.
2. Decide whether effect words denote exact traces, upper bounds, or semantic layers.
3. Give a small-step evaluation-context semantics and prove the two explicit-node rules agree with it.
4. Choose between head-normal and word-layer decomposition.
5. Only then define the extended graded monad's unit and bind.
