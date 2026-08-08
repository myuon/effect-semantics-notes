# Chapter I — metatheory and base certificate

## Status

**Paper proof package.**  This page extracts exactly what Chapter II may assume
when it adds free operations.

## 1. Syntactic substitution

### Lemma I.1 — value substitution

If

$$
\Gamma,x:A\vdash V:B
\qquad
\Gamma\vdash W:A,
$$

then

$$
\Gamma\vdash V[W/x]:B.
$$

### Lemma I.2 — computation substitution

If

$$
\Gamma,x:A\vdash M:C!b
\qquad
\Gamma\vdash W:A,
$$

then

$$
\Gamma\vdash M[W/x]:C!b.
$$

Both are proved simultaneously by induction on typing.  The primitive case
uses substitution only in its parameter; no continuation case exists.

## 2. Preservation and decomposition

### Theorem I.3 — internal preservation

If

$$
\Gamma\vdash M:A!b
\qquad
M\longrightarrow M',
$$

then

$$
\Gamma\vdash M':A!b.
$$

The $\beta$ and `let-return` cases use Lemma I.2.  Branch rules retain the
declared common effect.  Context closure uses associativity of graded
sequencing.

### Theorem I.4 — unique decomposition

Every closed well-typed base computation has a unique evaluation-position
decomposition as a return, an internal redex in its evaluation context, or an exposed base request
$\mathcal E[\beta(V)]$.

This is the effect-aware progress theorem used by later chapters.  It does not
call an exposed request “stuck,” and it does not assert that the request has a
unique response.

## 3. Termination

### Theorem I.5 — recursion-free machine normalization

Assume every element in the support of every base response is typed and each
recursion-free response branch is terminating.  Then every closed well-typed
Chapter-I program induces a well-defined outcome

$$
\mathsf{run}_{\mathcal K}(M)
\in\mathcal K(\mathsf{Obs}_B).
$$

Every branch in its support is a classified final observation.  No uniqueness
of the returned observation is asserted.

### Proof sketch

Use the standard reducibility argument for fine-grain CBV STLC, quantified over
every response in the support of $\mathsf{resp}_\beta$.  The primitive case is
reducible by the base-package branch-termination assumption.  Function,
product and sum cases are standard.  Unique decomposition identifies the
request; Kleisli composition in $\mathcal K$ combines its possible responses.

The theorem is deliberately absent from the Chapter-IV certificate.

## 4. Denotational soundness

### Lemma I.6 — semantic substitution

For a computation $M$,

$$
\llbracket M[W/x]\rrbracket
=
\llbracket M\rrbracket
\circ
\langle\mathsf{id},\llbracket W\rrbracket\rangle.
$$

The `let` case uses naturality of strength and multiplication.  The primitive
case is ordinary composition with $\beta^T$.

### Theorem I.7 — internal reduction soundness

If $M\to M'$, then

$$
\llbracket M\rrbracket=\llbracket M'\rrbracket.
$$

The principal equations are semantic substitution, the graded unit laws, and
coproduct elimination.  Context closure uses congruence of graded bind.

## 5. Effect upper-bound safety

### Theorem I.8

If

$$
\vdash M:A!b
$$

then every base primitive that the machine can execute is permitted by the
ordered upper bound $b$ at its typed position.  Effects in $b$ need not execute.

### Proof idea

Unique decomposition and residual-context typing show that an exposed
$\beta(V)$ occurs with primitive grade $|\beta|$ in the ordered position
assigned by the surrounding `let` contexts.  Internal reduction preserves the
declared bound.  Branch selection may remove potential effects but cannot add
an effect outside the common upper bound.  The selected base package separately
checks that its external response rule implements only the declared primitive.

This is a may-effect theorem.  It is intentionally one-way and introduces no
runtime trace object.

## 6. Adequacy schema

Choose a ground operational outcome
$\mathsf{run}_{\mathcal K}:M\mapsto\mathcal K(\mathsf{Obs}_B)$ and a
denotational observation $\mathsf{observe}$.  The base package is adequate at
ground type $G$ when

$$
\mathsf{run}_{\mathcal K}(M)
=\mathsf{observe}(\llbracket M\rrbracket)
$$

for every closed $M:G!b$.  In the deterministic case this reduces to the old
single-outcome equivalence.  One direction may be selected instead if the
later application needs only soundness or reflection; the certificate records
which.

### Writer instance

For the upper-bound Writer model,

$$
\langle M,\epsilon\rangle
\Downarrow_W
\langle\mathsf{return}\,V,w\rangle
\quad\Longleftrightarrow\quad
\mathsf{observe}(\llbracket M\rrbracket)=(w,V).
$$

The proof iterates the one-step invariant that accumulated machine log followed
by residual denotational log is constant.

### State instance

For every initial store $s$,

$$
\langle M,s\rangle
\Downarrow_S
\langle\mathsf{return}\,V,s'\rangle
$$

iff

$$
\llbracket M\rrbracket(s)=(V,s').
$$

### Exception instance

The denotation returns $\mathsf{inl}\,V$ exactly for a machine return and
$\mathsf{inr}\,e$ exactly for the terminal error $e$.  The proof follows
the short-circuiting bind equations.

### Random instance

For $\mathcal K=T=\mathsf{SubDist}$ and a fair primitive
$\mathsf{randomBool}:1\to\mathsf{Bool}$,

$$
\mathsf{run}_{\mathsf{SubDist}}(M)(o)
=\mathsf{observe}(\llbracket M\rrbracket)(o)
$$

for every ground outcome $o$.  Thus preservation and adequacy survive, while
the conclusion is equality of probability weights rather than uniqueness of
the returned value.

## 7. The Chapter-I structure theorem

### Definition I.1 — split base certificates

For a base calculus $L_B$, ordered effect algebra
$E_B=(B,1,\cdot,\leq)$ and response monad $\mathcal K$, define
$\mathsf{BaseSafetyCert}(L_B,E_B,\mathcal K)$ by:

1. **Operational metatheory.** Substitution and support-wise preservation hold,
   and each closed term has one selected return/redex/request position.
2. **Typed response structure.** Every primitive has a typed
   $\mathcal K$-response; every supported recursion-free branch terminates; and
   executed primitives are covered by the declared effect bound.

For a graded interpretation $T$, define
$\mathsf{BaseModelCert}(L_B,E_B,T)$ by:

1. **Graded semantic structure.** $T$ has return, multiplication, strength,
   coherent weakening and interpretations of all base primitives, satisfying
   the graded monad and weakening laws.
2. **Semantic soundness.** Semantic substitution and internal-reduction
   soundness hold.

Finally,
$\mathsf{BaseAdequacyCert}(L_B,\mathcal K,T,
\mathsf{obs}_B,\mathsf{observe}_T)$ means that primitive responses agree with
their denotational observations and closed ground operational and
denotational observations agree in $\mathcal K$. Retain the bundled name as

$$
\begin{aligned}
&\mathsf{BaseCert}(L_B,E_B,\mathcal K,T,\mathsf{obs}_B)\\
&\quad:\Longleftrightarrow
\mathsf{BaseSafetyCert}(L_B,E_B,\mathcal K)
\land\mathsf{BaseModelCert}(L_B,E_B,T)\\
&\qquad\land
\mathsf{BaseAdequacyCert}(L_B,\mathcal K,T,
\mathsf{obs}_B,\mathsf{observe}_T).
\end{aligned}
\tag{Base-Split}
$$

End-to-end examples may use `BaseCert`; transport theorems cite only the
component certificates they actually use.

For the recursion-free adequacy theorem, define
$\mathsf{FiniteResponseCert}(\mathcal K)$ by the following additional
conditions.

1. Every primitive response has finite support, and Kleisli composition of
   finitely supported responses is again finitely supported.
2. `map`, return and Kleisli composition satisfy the monad laws on these
   supports.
3. The return, terminal-base and free-request injections used by the
   observation object remain pairwise disjoint after applying $\mathcal K$.
4. Operation tags are reflected, and every response type quantified over by a
   free-request observation is finite.

This certificate is not part of `BaseModelCert`: it is needed only for the
finite observation tree and its reflection theorem. `Id`, finite powerset and
finitely supported subdistribution satisfy it for finite response types.

The `BaseSafetyCert` fields are written formally as follows:

$$
\begin{aligned}
\mathsf{subst}:&\quad
 \Gamma,x:A\vdash J\land\Gamma\vdash V:A
 \Rightarrow\Gamma\vdash J[V/x],\\
\mathsf{pres}:&\quad
 \Gamma\vdash M:A!b\land M'\in\operatorname{supp}(\mathsf{step}_B(M))
 \Rightarrow\Gamma\vdash M':A!b,\\
\mathsf{uniquePos}:&\quad
 \vdash M:A!b\Rightarrow
 \mathsf{Ret}(M)\mathbin{\dot\vee}\mathsf{Redex}(M)
 \mathbin{\dot\vee}\mathsf{BaseReq}(M),\\
\mathsf{resp}:&\quad
 \mathsf{resp}_\beta:P_\beta
 \to\mathcal K(R_\beta+\mathsf{Out}_\beta),\\
\mathsf{respTy}:&\quad
 z\in\operatorname{supp}(\mathsf{resp}_\beta(V))
 \Rightarrow\mathsf{TypedResponse}_\beta(z),\\
\mathsf{branchNorm}:&\quad
 \vdash M:A!b\Rightarrow
 \forall\pi\in\operatorname{suppRun}(M).\ \pi\text{ reaches an outcome},\\
\mathsf{effsafe}:&\quad
 \vdash M:A!b\land M\to_B^*\mathcal E[\beta(V)]\\
&\hspace{39mm}\Rightarrow
 \exists p,q.\ p\cdot|\beta|\cdot q\leq b.
\end{aligned}
$$

$\dot\vee$ denotes mutually exclusive alternatives.  `BaseModelCert` requires
the following semantic data:

$$
\eta_A:A\to T_1A,
\quad
\mu_{b,c,A}:T_bT_cA\to T_{b\cdot c}A,
\quad
\mathsf{st}_{b,X,A}:X\times T_bA\to T_b(X\times A),
$$

$$
\tau_{b,c,A}:T_bA\to T_cA\ (b\leq c),
\qquad
\beta^T:P_\beta\to T_{|\beta|}R_\beta.
$$

`monadlaw` contains the graded left/right unit and associativity equations;
`weaklaw` contains

$$
\tau_{b,b}=\mathsf{id},
\qquad
\tau_{c,d}\circ\tau_{b,c}=\tau_{b,d},
$$

and compatibility of $\tau$ with $\eta,\mu,\mathsf{st}$ and every
$\beta^T$. The remaining `BaseModelCert` fields are `semsubst` and `redsnd`;
`respSound` and `adequate` belong to `BaseAdequacyCert`:

$$
\begin{aligned}
\mathsf{semsubst}:&\quad
 \llbracket J[V/x]\rrbracket
 =\llbracket J\rrbracket\circ
   \langle\mathsf{id},\llbracket V\rrbracket\rangle,\\
\mathsf{redsnd}:&\quad
 M\to_{\mathsf{int}}M'\Rightarrow
 \llbracket M\rrbracket=\llbracket M'\rrbracket,\\
\mathsf{respSound}:&\quad
 \mathsf{observe}(\beta^T(V))
 =\mathsf{map}_{\mathcal K}(\mathsf{plug},\mathsf{resp}_\beta(V)),\\
\mathsf{adequate}:&\quad
 \mathsf{run}_{\mathcal K}(M)
 =\mathsf{observe}_T(\llbracket M\rrbracket)
 \quad(M\text{ closed and ground}).
\end{aligned}
$$

### Theorem I.9 — Base certificate extraction

For each $X\in\{\mathsf{Writer},\mathsf{State},\mathsf{Exception},
\mathsf{Random}\}$, let
$L_X,E_X,T^X,\mathsf{obs}_X$ be the syntax/machine, ordered algebra, model and
observation defined in this chapter, and let $\mathcal K_X$ be `Id` for the
first three instances and `SubDist` for `Random`.  Then

$$
\forall X\in\{W,S,E,R\}.\quad
\mathsf{BaseCert}(L_X,E_X,\mathcal K_X,T^X,\mathsf{obs}_X).
$$

### Proof

The fields `subst`, `pres`, `uniquePos`, `respTy`, `branchNorm`, and `effsafe` follow from
Theorems I.1–I.5 and I.8 after checking each primitive machine rule.  The
displayed Writer, State, Exception and Random constructions supply
$\eta,\mu,\mathsf{st},\tau,\beta^T$ and their laws.  Theorems I.6–I.7 supply
`semsubst` and `redsnd`; the four instance proofs above supply `respSound` and
`adequate`.
No free-operation or handler property is used. $\square$

## 8. Boundary exported to Chapter II

Complete derivations for the lemmas used above are given in
[Chapter I — detailed proofs](chapter-1-proof-details-v5.md).

`BaseCert` does not assert that every base has exact grades, that every
denotation exposes a syntactic head event, or that base effects commute with
future free operations.  Chapter II must add visible free-operation nodes
without inspecting an opaque base computation and must prove conservativity
through the supplied embedding.
