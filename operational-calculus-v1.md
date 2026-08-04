# Operational calculus v1

## Status

**Integration preview; not the current starting point.** Forward development now begins with [Base calculus v1](base-calculus-v1.md) and follows [Staged development](staged-development.md). This page introduced base operations, free operations, and handlers together and is retained as a later-stage reference.

このページではdenotational semanticsとeffect annotationをまだ定義しない。まず、どのprogramがどのhead formへ遷移し、shallow handlerが何を受け取るかだけを固定する。

後から導入するeffect systemは、このoperational semanticsに対してpreservationとprogressを満たさなければならない。意味論候補も、この挙動をsoundに表現するものだけを採用する。

## 1. Design choices

- fine-grain call-by-value
- valuesとcomputationsを構文的に分離
- simply typed、再帰なし
- operation nodeはcontinuationを明示する
- base operationsとfree operationsを構文上tagで区別する
- shallow handlerはfree interface $\Delta$ でindexする
- matching operationのcontinuationは同じhandlerで再処理しない
- base operationはforwardし、そのcontinuationではmatching operationの探索を続ける
- mismatching free operationの自動forwardingは導入しない
- effect indices、subeffecting、paddingはこの段階では導入しない

最後の三点は特に重要である。ここでは「標準的shallow handlingの動作」と「exact effect wordでその動作をどう型付けするか」を分離する。

## 2. Signatures

Base operation signatureを $\Sigma_B$ とする。各base operationは

$$
\beta:P_\beta\to R_\beta
\qquad(\beta\in\Sigma_B)
$$

という型を持つ。

Free-effect interfacesの集合を $\mathcal D$ とする。各 $\Delta\in\mathcal D$ は

$$
\operatorname{op}:P_{\operatorname{op}}\to R_{\operatorname{op}}
\qquad(\operatorname{op}\in\Delta)
$$

というoperation symbolsの族である。$\Sigma_B$ と各interfaceのoperation namesはdisjointにtag付けされているとする。

## 3. Types

Value typesを

$$
A,B ::= 1\mid\mathsf{Bool}\mid A\times B\mid A+B\mid A\to B\;\mathsf{comp}
$$

とする。現段階ではfunction typeにもcomputation judgmentにもeffect annotationを付けない。

## 4. Syntax

Values:

$$
\begin{aligned}
V,W ::= {}& x\mid *\mid\mathsf{true}\mid\mathsf{false}
\mid(V,W)\mid\mathsf{inl}\;V\mid\mathsf{inr}\;V\\
&\mid\lambda x.M.
\end{aligned}
$$

Computations:

$$
\begin{aligned}
M,N ::= {}& \mathsf{return}\;V
\mid\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N
\mid V\,W\\
&\mid\mathsf{if}\;V\;\mathsf{then}\;M\;\mathsf{else}\;N\\
&\mid\beta(V;y.M)\\
&\mid\operatorname{op}_\Delta(V;y.M)\\
&\mid\mathsf{handle}^{\mathsf{sh}}_\Delta M\;\mathsf{with}\;H.
\end{aligned}
$$

$\beta(V;y.M)$ と $\operatorname{op}_\Delta(V;y.M)$ はいずれもexplicit operation nodesである。parameterは $V$、operation resultは $y$ に束縛され、$M$ がresidual continuationである。

Handler syntaxは

$$
H=
\{\mathsf{return}\;x\mapsto M_r;\;
\operatorname{op}(p;k)\mapsto M_{\operatorname{op}}
\}_{\operatorname{op}\in\Delta}
$$

とする。base-operation clauseやgeneric forwarding clauseはhandler syntaxに含めない。

## 5. Unannotated typing

Judgmentsは

$$
\Gamma\vdash V:A
\qquad
\Gamma\vdash M:A\;\mathsf{comp}
$$

である。standard value rulesに加え、effect-relevantなrulesは次である。

$$
\frac{\Gamma\vdash V:A}
{\Gamma\vdash\mathsf{return}\;V:A\;\mathsf{comp}}
\tag{T-Return}
$$

$$
\frac{
\Gamma\vdash M:A\;\mathsf{comp}
\qquad
\Gamma,x:A\vdash N:B\;\mathsf{comp}}
{\Gamma\vdash\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N:B\;\mathsf{comp}}
\tag{T-Let}
$$

$$
\frac{
\beta:P\to R\in\Sigma_B
\quad\Gamma\vdash V:P
\quad\Gamma,y:R\vdash M:A\;\mathsf{comp}}
{\Gamma\vdash\beta(V;y.M):A\;\mathsf{comp}}
\tag{T-Base-Op}
$$

$$
\frac{
\operatorname{op}:P\to R\in\Delta
\quad\Gamma\vdash V:P
\quad\Gamma,y:R\vdash M:A\;\mathsf{comp}}
{\Gamma\vdash\operatorname{op}_\Delta(V;y.M):A\;\mathsf{comp}}
\tag{T-Free-Op}
$$

For a handler from $A$ to $C$, require

$$
\Gamma,x:A\vdash M_r:C\;\mathsf{comp}
$$

and, for every $\operatorname{op}:P\to R\in\Delta$,

$$
\Gamma,p:P,k:R\to A\;\mathsf{comp}
\vdash M_{\operatorname{op}}:C\;\mathsf{comp}.
$$

Then

$$
\frac{
\Gamma\vdash M:A\;\mathsf{comp}
\qquad \Gamma\vdash H:A\Rightarrow C}
{\Gamma\vdash
\mathsf{handle}^{\mathsf{sh}}_\Delta M\;\mathsf{with}\;H
:C\;\mathsf{comp}}.
\tag{T-Handle}
$$

このruleはinterface matchingをまだeffect indexで検査しない。matchingはreduction ruleで明示され、より精密なtyped ruleはeffect systemを載せる段階で導入する。

## 6. Head forms and observations

Computational head formsを

$$
Q ::= \mathsf{return}\;V
\mid\beta(V;y.M)
\mid\operatorname{op}_\Gamma(V;y.M)
$$

とする。closed computationは内部計算を終えると、valueをreturnするか、base/free operation requestを露出する。

Top-level semanticsがbase operationsを実行するか、traceとして観測するかは後からbase machineとしてparameterizeする。現在はbase operation nodeもobservable head formとして残す。

## 7. Small-step operational semantics

Reduction $M\longrightarrow N$ はcomputation contexts

$$
\mathcal E ::= [-]
\mid\mathsf{let}\;x\leftarrow\mathcal E\;\mathsf{in}\;N
\mid\mathsf{handle}^{\mathsf{sh}}_\Delta\mathcal E\;\mathsf{with}\;H
$$

の下で閉じる。

$$
\frac{M\longrightarrow M'}
{\mathcal E[M]\longrightarrow\mathcal E[M']}.
\tag{R-Context}
$$

Operation nodeのcontinuation $M$ の内部では、operation resultが返るまで先にreductionしない。したがって $\beta(V;y.M)$ と $\operatorname{op}_\Delta(V;y.M)$ はhead formsであり、sequencingまたはhandlerのprincipal ruleだけがその外側の構造を変える。principal rulesを以下に固定する。

### Pure computation

$$
(\lambda x.M)\,V\longrightarrow M[V/x]
\tag{R-Beta}
$$

$$
\mathsf{if}\;\mathsf{true}\;\mathsf{then}\;M\;\mathsf{else}\;N
\longrightarrow M
\tag{R-If-True}
$$

$$
\mathsf{if}\;\mathsf{false}\;\mathsf{then}\;M\;\mathsf{else}\;N
\longrightarrow N
\tag{R-If-False}
$$

$$
\mathsf{let}\;x\leftarrow\mathsf{return}\;V\;\mathsf{in}\;N
\longrightarrow N[V/x].
\tag{R-Let-Return}
$$

### Operation propagation through sequencing

For a base operation,

$$
\mathsf{let}\;x\leftarrow\beta(V;y.M)\;\mathsf{in}\;N
\longrightarrow
\beta(V;y.\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N).
\tag{R-Let-Base}
$$

For a free operation,

$$
\mathsf{let}\;x\leftarrow\operatorname{op}_\Gamma(V;y.M)\;\mathsf{in}\;N
\longrightarrow
\operatorname{op}_\Gamma
(V;y.\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N).
\tag{R-Let-Free}
$$

Usual capture-avoiding freshness conditions are implicit.

### Shallow handler: return

$$
\mathsf{handle}^{\mathsf{sh}}_\Delta
(\mathsf{return}\;V)\;\mathsf{with}\;H
\longrightarrow M_r[V/x].
\tag{R-Handle-Return}
$$

The return clause receives only $V$.

### Shallow handler: matching free operation

For $\operatorname{op}\in\Delta$,

$$
\mathsf{handle}^{\mathsf{sh}}_\Delta
(\operatorname{op}_\Delta(V;y.M))\;\mathsf{with}\;H
\longrightarrow
M_{\operatorname{op}}
[V/p,(\lambda y.M)/k].
\tag{R-Handle-Match}
$$

The captured continuation is

$$
k=\lambda y.M,
$$

not

$$
k=\lambda y.\mathsf{handle}^{\mathsf{sh}}_\Delta M\;\mathsf{with}\;H.
$$

This is the defining shallow behavior.

### Shallow handler: forwarding a base operation

$$
\mathsf{handle}^{\mathsf{sh}}_\Delta
(\beta(V;y.M))\;\mathsf{with}\;H
\longrightarrow
\beta
(V;y.\mathsf{handle}^{\mathsf{sh}}_\Delta M\;\mathsf{with}\;H).
\tag{R-Handle-Base}
$$

The base operation is not eliminated. The handler remains around its continuation so that it can reach the first matching $\Delta$-operation or the final return.

### Mismatching free operation

For $\Gamma\neq\Delta$, no rule is currently given for

$$
\mathsf{handle}^{\mathsf{sh}}_\Delta
(\operatorname{op}_\Gamma(V;y.M))\;\mathsf{with}\;H.
$$

This form is stuck relative to this handler and exposes the mismatch. Later, an effect typing rule should reject it unless an explicit forwarding construct or a handler-stack semantics is added.

## 8. Traces that distinguish return from a tail clause

Let

$$
\mathsf{tell}:\mathsf{String}\to1\in\Sigma_B
$$

and let $H_{\neg}$ have return clause

```text
return x -> return (not x)
```

Consider

```text
handle_Delta
  (tell("default"; u. return false))
with H_not
```

By `R-Handle-Base`,

```text
--> tell("default"; u.
      handle_Delta (return false) with H_not)
```

and by `R-Handle-Return`,

```text
--> tell("default"; u. return true)
```

Thus the handler's user-written return clause receives only `false`. It never receives the suspended `tell` computation. Operationally, the base operation is forwarded first and the return clause is applied later.

This calculation determines what a denotational semantics must do. If the no-$\Delta$ semantic branch contains $K(X)$, its elimination cannot be an arbitrary map $K(X)\to C$. It must model repeated base forwarding followed by the lifting of $h_{\mathsf{return}}:X\to C$.

## 9. Shallow continuation test

Let $\mathsf{coin}:1\to\mathsf{Bool}\in\Delta$ and consider

```text
handle_Delta
  coin((); x.
    tell("after coin"; u.
      coin((); y. return y)))
with H
```

The matching rule produces the operation clause with

```text
k = fun x ->
      tell("after coin"; u.
        coin((); y. return y))
```

If the clause invokes `k true`, the second `coin` is not automatically handled by $H$. This is the test that separates shallow from deep handling.

## 10. What is deliberately not fixed yet

The following belong to the next phase.

1. Whether exact effect indices classify all possible paths or individual operational paths.
2. How a no-operation path is assigned an index containing $\Delta$.
3. Whether such assignment is subeffecting, explicit padding, or a typed boundary constructor.
4. The output effect of a handler clause that ignores, invokes, or duplicates its continuation.
5. Whether mismatching free operations are rejected or explicitly forwarded.
6. The denotational representation $X+\mathsf{Op}_\Delta(K)$ versus $K+\mathsf{Op}_\Delta(K)$.

These questions must be answered by adding an effect system to this fixed operational core, rather than by changing the reduction rules to fit a preferred denotation.

## 11. Immediate proof obligations

- value substitution
- unannotated preservation
- deterministic decomposition into a reduction step or head form
- agreement between explicit operation nodes and an evaluation-context `perform` surface syntax
- trace calculations for return, one matching operation, two matching operations, a base prefix, and a mismatching interface
