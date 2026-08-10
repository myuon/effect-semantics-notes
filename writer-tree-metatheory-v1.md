# Writer tree metatheory v1

## Status

**Paper-level proof package for the recursion-free Writer + free-operation + shallow-handler model.**

This page proves the concrete properties that should later be generalized. It
uses the tree and trace-language definitions from
[Writer trace-graded trees v1](writer-trace-graded-trees-v1.md).

## 1. Concrete language fragment

Instantiate the base signature with

$$
\mathsf{tell}:\mathsf{String}\to1
$$

and retain arbitrary free interfaces $\Delta\in\mathcal D$. Computations have
the fixed direct CBV semantics, including exhaustive one-shot shallow handlers.

For this proof package, computation effects are downward-closed trace languages
$L$. Write

$$
\Gamma\vdash M:A!L.
$$

The ordinary rules become:

$$
\frac{\Gamma\vdash V:A}
{\Gamma\vdash\mathsf{return}\;V:A!1},
$$

$$
\frac{
\Gamma\vdash M:A!L
\qquad
\Gamma,x:A\vdash N:B!K
}{
\Gamma\vdash
\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N
:B!(L\otimes K)},
$$

and

$$
\frac{
\Gamma\vdash M:A!L
\qquad L\subseteq K
}{
\Gamma\vdash M:A!K}.
$$

The primitive effects have grades

$$
\mathsf{tell}(V):1!J(w)
$$

and

$$
\operatorname{op}_\Delta(V):R!J(\Delta).
$$

Conditionals and cases use a common upper bound; their least available bound is
the union of branch languages.

## 2. Handler typing at language grades

Suppose

$$
\Gamma\vdash M:A!L
$$

and every exhaustive clause has a common bound $K$:

$$
\Gamma,x_{\operatorname{op}}:P_{\operatorname{op}}
\vdash
N_{\operatorname{op}}:
R_{\operatorname{op}}!K.
$$

Then the sound rule is

$$
\frac{
\Gamma\vdash M:A!L
\qquad
\Gamma\vdash H:\Delta\Rightarrow K
}{
\Gamma\vdash
\mathsf{handle}_\Delta M\;\mathsf{with}\;H
:A!\Phi_{\Delta,K}(L)}.
\tag{T-Handle-Lang}
$$

This replaces the generally invalid single-word output $be'e$. When the
anchoring condition of the simple rule holds, one may subsequently widen
$\Phi_{\Delta,K}(J(b\Delta e))$ to a principal displayed word bound.

## 3. Denotational semantics

Contexts are interpreted as sets/products as in the Stage 0 Writer model. Values
retain their ordinary set interpretation.

For computations:

$$
\llbracket\mathsf{return}\;V\rrbracket\rho
=
\mathsf{ret}(\llbracket V\rrbracket\rho),
$$

$$
\llbracket
\mathsf{let}\;x\leftarrow M\;\mathsf{in}\;N
\rrbracket\rho
=
\llbracket M\rrbracket\rho
\mathbin{\mathsf{bind}}
(\lambda x.\llbracket N\rrbracket(\rho,x)),
$$

$$
\llbracket\mathsf{tell}(V)\rrbracket\rho
=
\mathsf{tell}
(\llbracket V\rrbracket\rho,\mathsf{ret}(*)),
$$

$$
\llbracket\operatorname{op}_\Delta(V)\rrbracket\rho
=
\mathsf{op}_\Delta
(\llbracket V\rrbracket\rho,
 \lambda r.\mathsf{ret}(r)).
$$

For an exhaustive handler, interpret each clause as

$$
c_{\operatorname{op}}(p)
=
\llbracket N_{\operatorname{op}}\rrbracket(\rho,p)
$$

and use the structural tree handler:

$$
\llbracket
\mathsf{handle}_\Delta M\;\mathsf{with}\;H
\rrbracket\rho
=
\mathsf{handle}_\Delta^c
(\llbracket M\rrbracket\rho).
$$

Subeffecting changes only the refinement proof, never the underlying tree.

## 4. Value substitution

### Lemma WM-001

For values,

$$
\llbracket W[V/x]\rrbracket\rho
=
\llbracket W\rrbracket
(\rho,\llbracket V\rrbracket\rho).
$$

For computations,

$$
\llbracket M[V/x]\rrbracket\rho
=
\llbracket M\rrbracket
(\rho,\llbracket V\rrbracket\rho).
$$

### Proof

Simultaneous induction on syntax. The handler case applies the induction
hypothesis to the scrutinee and every clause; the structural handler is a
function on the resulting trees and introduces no new environment dependency.
$\square$

## 5. Effect soundness

### Theorem WM-002

If

$$
\Gamma\vdash M:A!L,
$$

then for every $\rho\in\llbracket\Gamma\rrbracket$,

$$
\llbracket M\rrbracket\rho
\in
\mathsf{Tree}_L(\llbracket A\rrbracket).
$$

Equivalently,

$$
\mathsf{Tr}(\llbracket M\rrbracket\rho)
\subseteq L.
$$

### Proof

Induction on the typing derivation.

- Return follows from $\mathsf{Tr}(\mathsf{ret}(x))=1$.
- Let uses `WT-001`, the trace-of-bind lemma.
- `tell` has the single trace $\mathbf w\in J(w)$.
- A free operation has the single trace $\Delta\in J(\Delta)$.
- Branching uses the selected common upper bound; at the least bound, the
  selected branch lies in the union.
- Subeffecting is subset inclusion.
- Handler uses `WT-002` and `T-Handle-Lang`.

$\square$

### Corollary WM-003 — Old Writer grades embed soundly

If an old Writer-only derivation has grade $1$, its denotation has no `tell`
nodes. If it has grade $w$, its denotation may contain any finite number of
`tell` nodes, because

$$
J(w)=\{\mathbf w^n\mid n\geq0\}.
$$

Moreover,

$$
J(w\cdot w)=J(w)=J(w)\otimes J(w).
$$

Thus the trace refinement respects the old idempotent Writer multiplication.

## 6. Denotational reduction soundness

### Theorem WM-004

If

$$
M\longrightarrow M'
$$

is an internal direct-semantics reduction, then

$$
\llbracket M\rrbracket
=
\llbracket M'\rrbracket
$$

as underlying trees.

### Proof — ordinary cases

- β-reduction uses WM-001.
- `let-return` uses the left-unit law of tree bind and WM-001.
- Context closure uses congruence of bind.
- Boolean and sum cases select the same denotational branch.

### Proof — handler return

By definition,

$$
\mathsf{handle}_\Delta^c(\mathsf{ret}(v))
=
\mathsf{ret}(v).
$$

### Proof — handler match

Suppose the direct rule is

$$
\mathsf{handle}_\Delta
\mathcal E[\operatorname{op}_\Delta(V)]
\;\mathsf{with}\;H
\longrightarrow
\mathsf{let}\;r\leftarrow N[V/x]\;\mathsf{in}\;
\mathcal E[\mathsf{return}\;r].
$$

The denotation of the exposed request has the form

$$
\mathsf{op}_\Delta(p,k_\mathcal E).
$$

The left side becomes

$$
c_{\operatorname{op}}(p)
\mathbin{\mathsf{bind}}
k_\mathcal E.
$$

By WM-001, the right-side clause denotes
$c_{\operatorname{op}}(p)$, and the residual context denotes
$k_\mathcal E$. Its outer `let` therefore denotes the same bind.

### Proof — unmatched free request

For $\Gamma\neq\Delta$,

$$
\mathsf{handle}_\Delta^c
(\mathsf{op}_\Gamma(p,k))
=
\mathsf{op}_\Gamma(p,k).
$$

This agrees with direct forwarding and removal of the handler. $\square$

Base-machine responses are observational transitions, not internal tree
equalities; they are covered by adequacy below.

## 7. Operational behavior tree

Define $\mathsf{Beh}(M)$ for a closed recursion-free computation by running
deterministic internal and Writer-machine steps until the next dynamic head.

### Return

If execution performs Writer log $\ell=[s_1,\ldots,s_n]$ and returns $v$, set

$$
\mathsf{Beh}(M)
=
\mathsf{tell}(s_1,
 \cdots\mathsf{tell}(s_n,\mathsf{ret}(v))\cdots).
$$

### Free request

If execution first writes $\ell$ and then exposes

$$
\mathcal E[\operatorname{op}_\Gamma(p)],
$$

set

$$
\mathsf{Beh}(M)
=
\mathsf{tell}^*(\ell,
  \mathsf{op}_\Gamma
  (p,\lambda r.\mathsf{Beh}
    (\mathcal E[\mathsf{return}\;r]))).
$$

Because the language is recursion-free and each recursive call moves beyond one
syntactic free request on that path, this definition is well founded by the
reducibility/normalization argument used for Writer adequacy.

## 8. Tree adequacy

### Theorem WM-005 — Behavior-tree adequacy

For every closed well-typed recursion-free computation,

$$
\boxed{
\mathsf{Beh}(M)=\llbracket M\rrbracket.
}
$$

### Proof

By well-founded induction on the normalization measure and the number of
remaining free-operation nodes.

1. Internal steps preserve denotation by WM-004, so normalize to the first
   observable head without changing the tree.
2. Each Writer-machine step removes one active `tell` request and contributes
   exactly one leading `tell` node in both $\mathsf{Beh}$ and the denotation.
3. At return, both sides are $\mathsf{ret}(v)$ after the same Writer prefix.
4. At a free request, the primitive-operation denotation gives the same
   operation, parameter, and result-indexed continuations. Apply the induction
   hypothesis pointwise to every response $r$.

$\square$

### Corollary WM-006 — Ground Writer adequacy

If $M$ contains no unhandled free request, then

$$
M\Downarrow_W(\ell,v)
\quad\Longleftrightarrow\quad
\mathsf{run}_W(\llbracket M\rrbracket)=(\ell,v).
$$

For $v:\mathsf{Bool}$, the denotation therefore reflects both the exact ordered
log and the returned Boolean.

### Corollary WM-007 — Request adequacy

If operational execution first produces log $\ell$ and exposes

$$
\mathcal E[\operatorname{op}_\Gamma(p)],
$$

then the denotation has exactly the corresponding Writer prefix followed by

$$
\mathsf{op}_\Gamma
(p,\lambda r.\llbracket
\mathcal E[\mathsf{return}\;r]
\rrbracket).
$$

Conversely, such a denotational head implies the corresponding operational
request decomposition.

## 9. Handler adequacy

### Theorem WM-008

For every closed handled computation,

$$
\mathsf{Beh}
(\mathsf{handle}_\Delta M\;\mathsf{with}\;H)
=
\mathsf{handle}_\Delta^c
(\mathsf{Beh}(M)).
$$

### Proof

Combine WM-005 for the handled term and scrutinee with the compositional
denotational clause for `handle`. More explicitly, inspect the first dynamic
head of $M$:

- Writer head: both sides emit the same `tell` and continue searching;
- return: both use identity return;
- matching free head: both run the same clause tree and bind the same unhandled
  continuation;
- other free head: both preserve the request and continuation without
  reinstalling the handler.

$\square$

This theorem validates not only final results but the one-shot control behavior.

## 10. Conservativity over the old Writer model

Let $\mathsf{BaseTree}(X)$ be trees containing only `ret` and `tell`. The maps

$$
\mathsf{run}_W:\mathsf{BaseTree}(X)
\to
\mathsf{List}(\mathsf{String})\times X
$$

and

$$
\mathsf{quote}_W(\ell,x)
=
\mathsf{tell}^*(\ell,\mathsf{ret}(x))
$$

are mutually inverse:

$$
\mathsf{run}_W\circ\mathsf{quote}_W
=
\mathsf{id},
$$

$$
\mathsf{quote}_W\circ\mathsf{run}_W
=
\mathsf{id}.
$$

They preserve return and bind, so

$$
\mathsf{BaseTree}(X)
\cong
\mathsf{List}(\mathsf{String})\times X
$$

as monads. Under $J(1)$ and $J(w)$ this is also compatible with the old Writer
grading.

Thus, for Writer specifically, the free-tree model is not merely an adequacy
refinement: its base-only fragment recovers the original model up to canonical
isomorphism.

## 11. Naturality and structural lifting

### Lemma WM-009 — Handler naturality

For $f:X\to Y$,

$$
\mathsf{map}(f)
\circ
\mathsf{handle}_{\Delta,X}^c
=
\mathsf{handle}_{\Delta,Y}^c
\circ
\mathsf{map}(f),
$$

provided clause denotations are transformed at the same result type.

### Proof

Tree induction. The matching case uses associativity of bind and its compatibility
with map; the other cases are immediate. $\square$

### Structural relation

Given relations on values and operation parameters, lift them to trees by:

- related returns contain related values;
- `tell` nodes contain the same string and related tails;
- free nodes use the same qualified operation, related parameters, and
  pointwise related continuations.

Induction shows compatibility with return and bind. If corresponding handler
clauses are related, the two structural handlers preserve the lifted relation.

This is the concrete template for the later general relation-lifting theorem.

## 12. What has and has not been established

At paper level, the Writer model now supports:

- trace-language graded monad laws;
- sound embedding of the old Writer grades;
- proof-irrelevant subeffecting;
- effect soundness;
- internal reduction soundness;
- behavior-tree and ground Writer adequacy;
- request adequacy;
- shallow-handler adequacy;
- base conservativity up to canonical monad isomorphism;
- handler naturality;
- a structural relation-lifting template.

The proofs still need mechanization or fully expanded routine induction cases
for maximum assurance. The next mathematical task is to isolate exactly which
parts of this package use special properties of Writer and which require only a
base operation-tree interpretation.
