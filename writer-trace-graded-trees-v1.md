# Writer trace-graded trees v1

## Status

**Preferred concrete Stage 3 model.**

This page equips finite Writer interaction trees with proof-irrelevant ordered
trace-language grades and defines the shallow handler as a grade transformer.
It validates the adopted operational semantics without semantic padding nodes.

## 1. Runtime trees and static grades are separate

Runtime denotations are finite trees

$$
\begin{aligned}
t::={}&\mathsf{ret}(x)\\
&\mid\mathsf{tell}(s,t)\\
&\mid\mathsf{op}_\Gamma(p,k).
\end{aligned}
$$

Static grades do not occur as tree constructors. In particular, there is no
`skip` node.

This enforces proof irrelevance operationally:

> widening a grade changes only the set in which the same tree is classified.

## 2. Abstract event traces

Let the event alphabet be

$$
\mathcal A=\{\mathbf w\}+\mathcal D,
$$

where:

- $\mathbf w$ records one Writer/base event abstractly;
- $\Delta\in\mathcal D$ records one free request from interface $\Delta$.

The concrete string passed to `tell` and the operation parameter are retained in
the tree but erased from the effect trace.

A trace is a finite word

$$
q\in\mathcal A^*.
$$

Sequential order is word concatenation and is noncommutative.

## 3. Trace preorder and upper bounds

Write

$$
q\preceq q'
$$

when $q$ is obtained from $q'$ by deleting zero or more event tokens while
preserving the order of the remaining tokens. Thus

$$
\epsilon\preceq q
$$

and in particular

$$
\epsilon\preceq\Delta,
\qquad
\epsilon\preceq\mathbf w.
$$

This is the concrete upper-bound reading: an annotated event may be absent at
runtime.

The subsequence preorder is compatible with concatenation:

$$
q_1\preceq q_1',\quad q_2\preceq q_2'
\Longrightarrow
q_1q_2\preceq q_1'q_2'.
$$

For the idempotent Writer grade $w\cdot w=w$, one may additionally quotient a
nonempty consecutive block of $\mathbf w$ tokens to the single abstract grade
$w$. We keep event-level traces here because they make operational order and
induction explicit; the quotient to $\{1,w\}$ is given later by observation.

## 4. The grade quantale

A grade is a downward-closed trace language

$$
L\subseteq\mathcal A^*,
$$

meaning

$$
q'\in L,\ q\preceq q'
\Longrightarrow q\in L.
$$

Write $\downarrow S$ for downward closure. Define

$$
I=\{\epsilon\},
$$

$$
L\otimes K
=
\downarrow\{qr\mid q\in L,\ r\in K\},
$$

and joins by union:

$$
\bigvee_iL_i=\bigcup_iL_i.
$$

Ordered by inclusion, these grades form a unital quantale:

- $\otimes$ is associative;
- $I$ is its unit;
- arbitrary joins exist;
- multiplication preserves joins in each argument.

### Proof

Associativity and the unit law follow from word concatenation; downward closure
is idempotent and compatible with concatenation. Distribution follows because
setwise concatenation distributes over union. $\square$

Every concrete word $E$ embeds as the principal grade

$$
\langle E\rangle=\downarrow\{E\}.
$$

Then ordinary subeffecting is inclusion:

$$
E\preceq F
\Longrightarrow
\langle E\rangle\subseteq\langle F\rangle.
$$

## 5. Tree traces

Define the complete path traces of a finite tree:

$$
\mathsf{Tr}(\mathsf{ret}(x))
=
\{\epsilon\},
$$

$$
\mathsf{Tr}(\mathsf{tell}(s,t))
=
\{\mathbf wq\mid q\in\mathsf{Tr}(t)\},
$$

and

$$
\mathsf{Tr}(\mathsf{op}_\Gamma(p,k))
=
\bigcup_{r\in R_{\operatorname{op}}}
\{\Gamma q\mid q\in\mathsf{Tr}(k(r))\}.
$$

The grade-indexed carrier is a subset/refinement:

$$
\mathsf{Tree}_L(X)
=
\{t\in\mathsf{Tree}(X)mid
\mathsf{Tr}(t)\subseteq L\}.
$$

Subeffecting is literal inclusion:

$$
L\subseteq K
\Longrightarrow
\mathsf{Tree}_L(X)\subseteq\mathsf{Tree}_K(X).
$$

No map changes the underlying tree. Hence all padding proofs with the same
endpoints have identical denotations.

## 6. Graded monad structure

Return satisfies

$$
\mathsf{ret}:X\to\mathsf{Tree}_I(X).
$$

Tree bind is defined structurally as in
[Writer representation comparison v1](writer-representation-comparison-v1.md).

### Lemma WT-001 — Trace of bind

If

$$
\mathsf{Tr}(t)\subseteq L
$$

and

$$
\forall x.\ \mathsf{Tr}(f(x))\subseteq K,
$$

then

$$
\mathsf{Tr}(t\mathbin{\mathsf{bind}}f)
\subseteq
L\otimes K.
$$

### Proof

Induction on $t$.

- `ret`: the result is $f(x)$ and $I\otimes K=K$.
- `tell`: prepend $\mathbf w$ to every induction-hypothesis trace.
- `op`: prepend the interface token and apply the induction hypothesis
  pointwise to every response continuation.

Each resulting path is a path of $t$ followed by a path supplied by $f$, hence
lies in the downward closure of the concatenation language. $\square$

Therefore

$$
\mathsf{bind}_{L,K}:
\mathsf{Tree}_L(X)
\times
(X\to\mathsf{Tree}_K(Y))
\to
\mathsf{Tree}_{L\otimes K}(Y).
$$

The monad laws hold as equalities of underlying trees by structural induction.
Thus $L\mapsto\mathsf{Tree}_L$ is a graded monad over the trace-language
quantale.

## 7. Primitive operations

Writer output is interpreted by

$$
\mathsf{tell}(s)
=
\mathsf{tell}(s,\mathsf{ret}(*))
\in
\mathsf{Tree}_{\langle\mathbf w\rangle}(1).
$$

For $\operatorname{op}:P\to R\in\Delta$,

$$
\operatorname{op}_\Delta(p)
=
\mathsf{op}_\Delta
(p,\lambda r.\mathsf{ret}(r))
\in
\mathsf{Tree}_{\langle\Delta\rangle}(R).
$$

The continuation still arises through bind, not as a source argument.

## 8. First-free-head trace transformer

Let the exhaustive $\Delta$ clauses share grade $K$. For a single trace $q$,
find its first free-interface token, ignoring an initial block of Writer tokens.

Define $\phi_{\Delta,K}(q)$ as follows.

### No free token

If $q\in\{\mathbf w\}^*$, then

$$
\phi_{\Delta,K}(q)=\{q\}.
$$

### Matching first free token

If

$$
q=u\Delta v,
\qquad
u\in\{\mathbf w\}^*,
$$

and this displayed $\Delta$ is the first free token, define

$$
\phi_{\Delta,K}(q)
=
\{urv\mid r\in K\}.
$$

The clause trace $r$ replaces the handled request after the already executed
Writer prefix $u$ and before the resumed tail $v$.

### Other first free token

If

$$
q=u\Gamma v,
\qquad
\Gamma\neq\Delta,
$$

with $\Gamma$ first among free tokens, define

$$
\phi_{\Delta,K}(q)=\{q\}.
$$

Forwarding changes nothing and stops the handler.

Lift this pointwise to grades:

$$
\boxed{
\Phi_{\Delta,K}(L)
=
\downarrow
\bigcup_{q\in L}
\phi_{\Delta,K}(q).
}
$$

This is monotone in both $L$ and $K$.

## 9. Handler definition

Assume exhaustive clauses

$$
c_{\operatorname{op}}:
P_{\operatorname{op}}
\to
\mathsf{Tree}_K(R_{\operatorname{op}}).
$$

Define $\mathsf{handle}_\Delta$ on underlying trees by:

$$
\mathsf{handle}_\Delta(\mathsf{ret}(x))
=
\mathsf{ret}(x),
$$

$$
\mathsf{handle}_\Delta(\mathsf{tell}(s,t))
=
\mathsf{tell}(s,\mathsf{handle}_\Delta(t)),
$$

$$
\mathsf{handle}_\Delta
(\mathsf{op}_\Delta(p,k))
=
c_{\operatorname{op}}(p)
\mathbin{\mathsf{bind}}
k,
$$

$$
\mathsf{handle}_\Delta
(\mathsf{op}_\Gamma(p,k))
=
\mathsf{op}_\Gamma(p,k)
\qquad(\Gamma\neq\Delta).
$$

Recursion occurs only through Writer nodes while searching for the first actual
free head. Neither free-operation case recursively handles its continuation.

## 10. Handler grading theorem

### Theorem WT-002

The tree handler restricts to a map

$$
\boxed{
\mathsf{handle}_{\Delta,L,K}:
\mathsf{Tree}_L(X)
\to
\mathsf{Tree}_{\Phi_{\Delta,K}(L)}(X).
}
$$

### Proof

Induction on the input tree.

- `ret`: the only trace is $\epsilon$, handled by the no-free-token case.
- `tell`: prepend $\mathbf w$ and apply the induction hypothesis; the definition
  of $\phi$ preserves the initial Writer prefix.
- matching `op`: every input path is $\Delta v$. Tree bind replaces this token
  by a clause path $r\in K$ followed by the corresponding continuation path
  $v$, yielding $rv$.
- other `op`: the tree and all traces are unchanged by both the tree handler and
  $\phi$.

Downward closure covers widened input and clause bounds. $\square$

## 11. Recovery and failure of the simple word formula

For a principal input word

$$
b\Delta e
$$

where $b$ contains only Writer tokens, the original hoped-for output was

$$
bKe.
$$

This is valid if every matching runtime trace uses the displayed $\Delta$ as
its first actual free token. Then $\Phi$ simply replaces that token.

It fails without that anchoring condition. Consider the upper bound

$$
\Delta\mathbf w\Delta
$$

and the runtime trace

$$
\mathbf w\Delta,
$$

which skips the first optional $\Delta$. The handler produces

$$
\mathbf wK,
$$

not a trace necessarily bounded by

$$
K\mathbf w\Delta.
$$

Noncommutativity prevents moving $K$ before the already executed Writer event.

The language transformer $\Phi$ includes the correct $\mathbf wK$ alternative
without imposing a false reordering equation.

## 12. Writer observation and adequacy target

For a tree with no free nodes, define

$$
\mathsf{run}_W(\mathsf{ret}(x))=([],x),
$$

$$
\mathsf{run}_W(\mathsf{tell}(s,t))
=
(s::\ell,x)
\quad\text{when }\mathsf{run}_W(t)=(\ell,x).
$$

The next adequacy theorem should state:

> if a closed program evaluates under the Writer machine to log $\ell$ and
> value $v$, then its tree denotation is base-only and runs to $(\ell,v)$; and
> conversely.

For programs exposing a free request, the tree root after its Writer prefix
must agree with the direct request decomposition. Handler adequacy then follows
from `WT-002` plus the four defining tree equations.

## 13. Consequences

This construction provides:

1. proof-irrelevant uppercasting by subset inclusion;
2. ordered, noncommutative effect information;
3. arbitrary joins needed for alternative handler outcomes;
4. a graded monad of finite interaction trees;
5. a total grade transformer for the one-shot shallow handler;
6. no semantic middle-splitting requirement;
7. no confusion between skip and final return.

The price is that grades are trace languages rather than the original free
product words. Principal words still embed, but handler output may require a
non-principal language.

This suggests a two-level presentation:

- infer/display principal word grades when $\Phi$ returns a principal bound;
- use trace-language grades in the semantic metatheory and for genuinely
  non-principal handler outcomes.
