# Baseline calculus v1

## Status

**Superseded by [Exact-layer calculus v2](exact-layer-calculus-v2.md).**

> **Historical diagnosis:** this version incorrectly treated the extended index as an upper bound. The current main line treats it as an exact alternating layer structure.

この calculus は元の修論の再現ではない。今後の意味論、保存定理、反例を比較するために固定する最小言語である。必要が生じた場合は規則を黙って変更せず、v2 を作り差分を記録する。

## 1. Design choices

- fine-grain call-by-value
- values と computations を分離
- simply typed、再帰なし
- operation node は continuation を明示する
- handler は shallow
- effect composition は順序を保存し、一般には非可換
- effect annotation は exact trace ではなく安全な上界
- subeffecting の証明は観測されない
- deep handlers、effect polymorphism、dynamic instances は対象外

## 2. Effect algebra

Effect annotations は preordered monoid

$$
(E,\cdot,1,\leq)
$$

の元とする。

要求する法則:

$$
(e\cdot f)\cdot g=e\cdot(f\cdot g),
\qquad
1\cdot e=e=e\cdot 1,
$$

$$
e\leq e',\ f\leq f'
\Longrightarrow
e\cdot f\leq e'\cdot f'.
$$

各 free-effect interface $\Delta$ には distinguished grade

$$
[\Delta]\in E
$$

を対応させる。現時点では $E$ を base effects と interfaces の交互列に限定しない。

### Intended reading

$$
e\cdot f
$$

は「先に $e$、次に $f$」という順序付き上界である。annotation 内に $[\Delta]$ があっても、実行時に必ず operation が発生するとは限らない。

## 3. Signatures

Interface $\Delta$ は operation symbols の有限族である。

$$
\operatorname{op}:P_{\operatorname{op}}\to R_{\operatorname{op}}
\qquad(\operatorname{op}\in\Delta).
$$

異なる interfaces の operation names は、必要なら tag により disjoint とする。

## 4. Types and contexts

Value types:

$$
A,B,C ::= 1 \mid A\times B \mid A+B \mid A\to(B!e).
$$

$A\to(B!e)$ は、値を受け取り effect $e$ の computation を返す value function type である。

Contexts are finite lists

$$
\Gamma=x_1:A_1,\ldots,x_n:A_n.
$$

## 5. Syntax

Values:

$$
\begin{aligned}
V,W ::= {}& x \mid * \mid (V,W) \mid \mathsf{fst}\;V \mid \mathsf{snd}\;V \\
&\mid \mathsf{inl}\;V \mid \mathsf{inr}\;V \mid \lambda x.M.
\end{aligned}
$$

Computations:

$$
\begin{aligned}
M,N ::= {}& \mathsf{return}\;V \\
&\mid \mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N \\
&\mid V\,W \\
&\mid \mathsf{case}\;V\;\mathsf{of}\;
  \mathsf{inl}\;x\Rightarrow M\mid\mathsf{inr}\;y\Rightarrow N \\
&\mid \operatorname{op}(V;y.M) \\
&\mid \mathsf{handle}^{\mathsf{sh}}_\Delta M\;\mathsf{with}\;H.
\end{aligned}
$$

A handler has clauses

$$
H=
\{\mathsf{return}\;x\mapsto M_r;\;
\operatorname{op}(p;k)\mapsto M_{\operatorname{op}}
\}_{\operatorname{op}\in\Delta}.
$$

The calculus uses explicit operation nodes. A surface form `perform op V` may later be defined by elaboration.

## 6. Value typing

We use standard simply typed rules for variables, unit, products, and sums. The effect-relevant abstraction rule is

$$
\frac{\Gamma,x:A\vdash M:B!e}
{\Gamma\vdash\lambda x.M:A\to(B!e)}.
$$

## 7. Computation typing

### Return

$$
\frac{\Gamma\vdash V:A}
{\Gamma\vdash\mathsf{return}\;V:A!1}.
\tag{T-Return}
$$

### Sequencing

$$
\frac{
\Gamma\vdash M:A!e
\qquad
\Gamma,x:A\vdash N:B!f}
{\Gamma\vdash
\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N
:B!(e\cdot f)}.
\tag{T-Let}
$$

### Application

$$
\frac{
\Gamma\vdash V:A\to(B!e)
\qquad
\Gamma\vdash W:A}
{\Gamma\vdash V\,W:B!e}.
\tag{T-App}
$$

### Case

$$
\frac{
\Gamma\vdash V:A+B
\quad
\Gamma,x:A\vdash M:C!e
\quad
\Gamma,y:B\vdash N:C!e}
{\Gamma\vdash
\mathsf{case}\;V\;\mathsf{of}\;
\mathsf{inl}\;x\Rightarrow M\mid\mathsf{inr}\;y\Rightarrow N
:C!e}.
\tag{T-Case}
$$

Branches with different effects may first be widened to a common upper bound.

### Operation node

$$
\frac{
\operatorname{op}:P\to R\in\Delta
\quad
\Gamma\vdash V:P
\quad
\Gamma,y:R\vdash M:A!e}
{\Gamma\vdash\operatorname{op}(V;y.M):A!([\Delta]\cdot e)}.
\tag{T-Op}
$$

### Subeffecting

$$
\frac{
\Gamma\vdash M:A!e
\qquad e\leq f}
{\Gamma\vdash M:A!f}.
\tag{T-Sub}
$$

## 8. Handler typing

The handler removes one exposed leading $\Delta$-operation. It does not recursively handle operations in the captured continuation.

Suppose

$$
\Gamma\vdash M:A!([\Delta]\cdot e).
$$

The return clause and every operation clause must have a common result type and effect:

$$
\Gamma,x:A\vdash M_r:C!f,
$$

$$
\Gamma,p:P_{\operatorname{op}},
k:R_{\operatorname{op}}\to(A!e)
\vdash M_{\operatorname{op}}:C!f.
$$

Then

$$
\frac{
\Gamma\vdash M:A!([\Delta]\cdot e)
\quad
\Gamma,x:A\vdash M_r:C!f
\quad
\bigl(
\Gamma,p:P_{\operatorname{op}},
k:R_{\operatorname{op}}\to(A!e)
\vdash M_{\operatorname{op}}:C!f
\bigr)_{\operatorname{op}\in\Delta}}
{\Gamma\vdash
\mathsf{handle}^{\mathsf{sh}}_\Delta M\;\mathsf{with}\;H
:C!f}.
\tag{T-Handle-Shallow}
$$

### Why the tail effect occurs in the continuation type

The continuation begins after the exposed operation. Hence it has latent effect $e$:

$$
k:R_{\operatorname{op}}\to(A!e).
$$

If a clause invokes $k$, ordinary application and sequencing charge $e$ to the clause body. If it ignores $k$, the tail effect need not appear in the inferred clause effect. The common $f$ is therefore an upper bound chosen after typing all clauses.

### Limitation

This rule only handles computations whose annotation has a leading $[\Delta]$. Handling under a base prefix $b$, as in $b\cdot[\Delta]\cdot e$, is not a primitive syntax rule in v1. That modular lifting is precisely a later semantic construction to investigate.

## 9. Reduction rules

The relation $M\longrightarrow N$ is closed under the computation contexts required by fine-grain CBV. Its principal rules are as follows.

### Beta and sequencing

$$
(\lambda x.M)\,V\longrightarrow M[V/x].
\tag{R-Beta}
$$

$$
\mathsf{let}\;x\leftarrow\mathsf{return}\;V\;\mathsf{in}\;N
\longrightarrow N[V/x].
\tag{R-Let-Return}
$$

### Operation propagation through sequencing

$$
\mathsf{let}\;x\leftarrow
\operatorname{op}(V;y.M)
\;\mathsf{in}\;N
\longrightarrow
\operatorname{op}
(V;y.\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N),
\tag{R-Let-Op}
$$

with the usual freshness conditions.

The typing is preserved because

$$
([\Delta]\cdot e)\cdot f
=
[\Delta]\cdot(e\cdot f).
$$

### Shallow handler: return

$$
\mathsf{handle}^{\mathsf{sh}}_\Delta
(\mathsf{return}\;V)\;\mathsf{with}\;H
\longrightarrow
M_r[V/x].
\tag{R-Handle-Return}
$$

The input may have been assigned $[\Delta]\cdot e$ by subeffecting even though it returns without performing an operation.

### Shallow handler: matching operation

$$
\mathsf{handle}^{\mathsf{sh}}_\Delta
(\operatorname{op}(V;y.M))\;\mathsf{with}\;H
\longrightarrow
M_{\operatorname{op}}
[V/p,(\lambda y.M)/k].
\tag{R-Handle-Op}
$$

Crucially,

$$
k:=\lambda y.M,
$$

not

$$
k:=\lambda y.
\mathsf{handle}^{\mathsf{sh}}_\Delta M\;\mathsf{with}\;H.
$$

## 10. Meta-properties to prove

### M-001 — Substitution

Value substitution preserves value and computation typing.

### M-002 — Weakening

Context weakening preserves typing.

### M-003 — Effect coherence

Different derivations using `T-Sub` give the same denotation. This will require coherent semantic coercions

$$
\tau_{e,f}:T_e\Rightarrow T_f.
$$

### M-004 — Preservation

If

$$
\Gamma\vdash M:A!e
\quad\text{and}\quad
M\longrightarrow N,
$$

then

$$
\Gamma\vdash N:A!e.
$$

The statement uses the same upper-bound effect $e$, not necessarily the smallest effect inferable for $N$.

### M-005 — Progress modulo operations

A closed well-typed computation is one of:

- reducible;
- $\mathsf{return}\;V$;
- an exposed operation node $\operatorname{op}(V;y.M)$.

An exposed operation is an observable suspended computation, not a stuck error.

**Status: blocked for Baseline v1 as written.** Unrestricted subeffecting may assign $[\Delta]\cdot e$ to a computation whose exposed operation belongs to another interface, while the handler has no forwarding rule. This is a mathematical defect in v1, not merely a missing proof.

## 11. Operational observations

For the first adequacy theorem, observations are head forms:

$$
M\Downarrow\mathsf{return}\;V
$$

or

$$
M\Downarrow\operatorname{op}(V;y.N).
$$

Contextual equivalence and complete abstraction are explicitly postponed.

## 12. Relationship to the word-layer proposal

Baseline v1 gives $[\Delta]\cdot e$ an operational, leading-operation interpretation. It does not yet justify the earlier candidate

$$
T_b(\widehat T_eX+\mathsf{Op}_\Delta(\widehat T_eX)).
$$

That expression may instead describe a handler operating underneath a base prefix or a designated semantic layer. The planned comparison is:

1. give v1 a head-normal denotation;
2. separately define the word-layer construction;
3. ask whether the layer construction implements a derived handler-under-prefix operation for v1.

## 13. Next semantic task

Define the minimum semantic structure interpreting v1:

- a strong $E$-graded monad $T$;
- coherent subeffect maps;
- interpretations of operation symbols;
- a semantic object representing exposed head operations;
- shallow-handler clause interpretation.

The first target is soundness of `R-Let-Op` and `R-Handle-Op`, not adequacy.
