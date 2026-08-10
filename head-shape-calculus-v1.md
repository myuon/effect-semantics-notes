# Head-shape calculus v1

## Status

**Archived diagnostic.** Baseline v1 のupper-bound解釈を修正するための探索だった。現在のmain lineでは、typed free layer自体がreturn/operation/residual continuationを保持するため、独立したhead-shape indexは採用しない。

## 1. The common operational problem

Shallow handler

$$
\mathsf{handle}^{\mathsf{sh}}_\Delta M\;\mathsf{with}\;H
$$

が一歩進むためには、$M$ の現在の head form が少なくとも次のどれかだと分かる必要がある。

1. $\mathsf{return}\;V$
2. matching operation $\operatorname{op}_\Delta(V;y.N)$
3. nonmatching operation $\operatorname{op}_\Gamma(V;y.N)$

Baseline v1 は effect upper bound $[\Delta]\cdot e$ から 1 または 2 を推測した。しかし上界は実際の head form を決定しない。

## 2. Repair A: rows plus forwarding

標準的な coarse effect row を有限集合

$$
\rho\subseteq\mathsf{Interfaces}
$$

として持つ。operation node は

$$
\frac{
\operatorname{op}\in\Delta
\quad
\Gamma,y:R\vdash M:A!\rho
}
{
\Gamma\vdash\operatorname{op}(V;y.M):A!(\{\Delta\}\cup\rho)
}
$$

と型付けする。

Handler が対象としない interface $\Gamma\neq\Delta$ を先頭に見た場合、forwarding rule を使う。

$$
\begin{aligned}
&\mathsf{handle}^{\mathsf{sh}}_\Delta
(\operatorname{op}_\Gamma(V;y.M))
\;\mathsf{with}\;H \\
&\qquad\longrightarrow
\operatorname{op}_\Gamma
(V;y.\mathsf{handle}^{\mathsf{sh}}_\Delta M\;\mathsf{with}\;H).
\end{aligned}
$$

ここで handler は nonmatching operation の continuation の周囲に残る。matching operation に到達した時点ではじめて、その continuation を handler で包まず clause に渡す。

### Strengths

- progress を自然に回復できる
- 標準的な extensible handlers の振る舞いに近い
- unordered な「起こりうる operations」の追跡には十分

### Weaknesses for the present goal

- $\Delta$ の後に $\Gamma$ が起こるのか、逆順かを区別しない
- 一つの matching operation を処理した後の residual effect を精密に表しにくい
- idempotent row では、同じ interface の最初の occurrence を除いても row が変わらない
- 「base effect の下に handler を持ち上げる」という順序構造が見えにくい

## 3. Repair B: a separate head-shape index

Interface labels の集合を $L$ とし、return head を表す特別な記号を $\checkmark$ とする。

A head shape is a set

$$
s\subseteq\{\checkmark\}+L.
$$

Intended meaning:

- $\checkmark\in s$: computation は head return になりうる
- $\Delta\in s$: computation は head $\Delta$-operation になりうる
- $s=\varnothing$: inhabitant がない、または到達不能な computation

Typing judgments become

$$
\Gamma\vdash M:A!e\;\triangleright s.
$$

$e$ は全体の sequential effect upper bound、$s$ は現在観測可能な head form の upper bound である。

## 4. Sequential composition of head shapes

Sequencing

$$
\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N
$$

の head は次のように決まる。

- $M$ が operation を露出すれば、それが全体の head
- $M$ が return すれば、$N$ の head が全体の head

そこで shape composition を

$$
s\blacktriangleright t
=
(s\setminus\{\checkmark\})
\cup
\begin{cases}
t & \checkmark\in s,\\
\varnothing & \checkmark\notin s
\end{cases}
$$

と定義する。

Identity candidate is

$$
\mathbf r=\{\checkmark\}.
$$

## 5. Algebraic laws of shapes

### Left identity

$$
\mathbf r\blacktriangleright t
=
\varnothing\cup t=t.
$$

### Right identity

If $\checkmark\notin s$, then

$$
s\blacktriangleright\mathbf r=s.
$$

If $\checkmark\in s$, then

$$
s\blacktriangleright\mathbf r
=(s\setminus\{\checkmark\})\cup\{\checkmark\}=s.
$$

### Associativity

We compare

$$
(s\blacktriangleright t)\blacktriangleright u
$$

and

$$
s\blacktriangleright(t\blacktriangleright u).
$$

If $\checkmark\notin s$, both sides are $s$.

Suppose $\checkmark\in s$. Both sides contain all non-return heads of $s$ and $t$. They contain heads of $u$ exactly when $\checkmark\in t$. More explicitly,

$$
(s\setminus\{\checkmark\})
\cup(t\setminus\{\checkmark\})
\cup
\begin{cases}
u & \checkmark\in t,\\
\varnothing & \checkmark\notin t.
\end{cases}
$$

is the normal form of both sides.

Therefore

$$
(s\blacktriangleright t)\blacktriangleright u
=
s\blacktriangleright(t\blacktriangleright u).
$$

### Monotonicity

For subset ordering,

$$
s\subseteq s',\quad t\subseteq t'
\Longrightarrow
s\blacktriangleright t
\subseteq
s'\blacktriangleright t'.
$$

The only nontrivial case is when $\checkmark$ is newly added in $s'$. This only adds the possible heads $t'$, so inclusion still holds.

**Derived conclusion.** Head shapes form a noncommutative preordered monoid

$$
(\mathcal P(\{\checkmark\}+L),
\blacktriangleright,
\{\checkmark\},
\subseteq).
$$

## 6. Refined typing rules

### Return

$$
\frac{\Gamma\vdash V:A}
{\Gamma\vdash\mathsf{return}\;V:A!1\triangleright\{\checkmark\}}.
$$

### Operation

$$
\frac{
\operatorname{op}:P\to R\in\Delta
\quad
\Gamma\vdash V:P
\quad
\Gamma,y:R\vdash M:A!e\triangleright s
}
{
\Gamma\vdash\operatorname{op}(V;y.M):
A!([\Delta]\cdot e)\triangleright\{\Delta\}
}.
$$

The continuation shape $s$ is latent behind the exposed operation. It belongs in the continuation function type but not in the current head shape.

### Sequencing

$$
\frac{
\Gamma\vdash M:A!e\triangleright s
\quad
\Gamma,x:A\vdash N:B!f\triangleright t
}
{
\Gamma\vdash
\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N:
B!(e\cdot f)\triangleright(s\blacktriangleright t)
}.
$$

### Subeffecting and shape weakening

$$
\frac{
\Gamma\vdash M:A!e\triangleright s
\quad e\leq f
\quad s\subseteq t
}
{
\Gamma\vdash M:A!f\triangleright t
}.
$$

Effect weakening cannot change the shape by itself; shape widening must be stated separately.

## 7. Refined function types

Continuation の latent behavior を保存するため value function type を

$$
A\to(B!e\triangleright s)
$$

とする。

Operation clause に渡る continuation は

$$
k:R\to(A!e\triangleright s)
$$

であり、$s$ は operation node の body に由来する。

This fixes a loss of information in Baseline v1, where only the continuation effect $e$ was retained.

## 8. Handler typing without forwarding

Handler input shape が

$$
s\subseteq\{\checkmark,\Delta\}
$$

を満たすとき、実行時 head は return または matching $\Delta$-operation に限られる。したがって forwarding rule は不要である。

Suppose

$$
\Gamma\vdash M:A!e\triangleright s,
\qquad
s\subseteq\{\checkmark,\Delta\}.
$$

For the return clause,

$$
\Gamma,x:A\vdash M_r:C!f\triangleright u_r.
$$

For each operation clause, the continuation type records its own latent grade and shape:

$$
\Gamma,p:P,
k:R\to(A!e_k\triangleright s_k)
\vdash M_{\operatorname{op}}:C!f\triangleright u_{\operatorname{op}}.
$$

The result shape can be widened to

$$
u=u_r\cup\bigcup_{\operatorname{op}\in\Delta}u_{\operatorname{op}}.
$$

Then

$$
\Gamma\vdash
\mathsf{handle}^{\mathsf{sh}}_\Delta M\;\mathsf{with}\;H
:C!f\triangleright u.
$$

### Remaining precision problem

The single input annotation $e$ does not by itself reveal the latent pair $(e_k,s_k)$ behind each possible operation head. A shape set says **which** interface may occur, but not the residual computation type after it occurs.

Therefore a plain head set is sufficient for progress but not yet sufficient for precise handler typing.

## 9. Residual-aware shapes

The information really needed by a shallow handler resembles a one-step transition description:

$$
\checkmark:A
$$

or, for each operation,

$$
\Delta(P,R;e_k,s_k).
$$

This suggests replacing the unparameterized set $s$ by a typed head signature carrying residual grades/shapes. Categorically, this is closer to a polynomial container

$$
X+
\coprod_{\operatorname{op}:P\to R}
P\times(T_{e_k,s_k}X)^R
$$

than to an ordinary effect row.

**Current assessment.** The simple shape monoid solves the operational progress defect and provides a useful abstraction, but precise shallow-handler semantics requires a residual-aware refinement.

## 10. Three test programs

Let $\Delta$ contain $\mathsf{ask}:1\to\mathsf{Bool}$ and $\Gamma$ contain $\mathsf{log}:\mathsf{String}\to1$.

### P-001 — Return then ask

$$
\mathsf{let}\;x\leftarrow\mathsf{return}\;*\;\mathsf{in}\;
\mathsf{ask}(*;b.\mathsf{return}\;b).
$$

Shapes:

$$
\{\checkmark\}\blacktriangleright\{\Delta\}
=\{\Delta\}.
$$

### P-002 — Log then ask

$$
\mathsf{log}(m;u.\mathsf{ask}(*;b.\mathsf{return}\;b)).
$$

The current head shape is

$$
\{\Gamma\},
$$

not $\{\Delta\}$. A handler requiring

$$
s\subseteq\{\checkmark,\Delta\}
$$

is correctly rejected unless handler-under-prefix/forwarding is used.

### P-003 — Ask then log

$$
\mathsf{ask}(*;b.\mathsf{log}(m;u.\mathsf{return}\;b)).
$$

The current head shape is $\{\Delta\}$, while the captured continuation has latent head shape $\{\Gamma\}$. A shallow $\Delta$-handler is accepted, and invoking $k$ exposes the unhandled $\Gamma$ operation.

Rows assign the same set $\{\Delta,\Gamma\}$ to P-002 and P-003. Head shapes distinguish them.

## 11. Comparison

| Property | Rows + forwarding | Sequential grade + head shape |
|---|---|---|
| Tracks possible operations | Yes | Yes, at current head |
| Tracks order | No | Yes, one observable step |
| Progress for handlers | By forwarding | By shape restriction |
| Residual continuation | Coarse | Can be refined explicitly |
| Handler under unrelated prefix | Operational forwarding | Separate lifting theorem |
| Fits original modular-extension question | Partly | Strongly |
| Mathematical cost | Lower | Higher |

## 12. Provisional direction

Keep both levels:

1. use rows + forwarding as the standard comparison calculus;
2. use head shapes as an abstraction of observable one-step structure;
3. refine shapes to residual-aware polynomial descriptions only where precise handler typing requires them.

The next question is whether residual-aware shapes are merely the datatype presentation of the free shallow layer already under consideration. If so, a separate novel type system may be unnecessary: the semantic extension itself supplies the required shape.
