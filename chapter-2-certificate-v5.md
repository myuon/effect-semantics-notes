# Chapter II — preservation proofs and `FreeCert`

## Status

**Conditional paper theorem.**  This page proves the recursion-free free
extension properties relative to the explicit `BaseCert` and initial-algebra
hypotheses.

## 1. Substitution and preservation

### Lemma II.1 — substitution

The Chapter-I value/computation substitution lemmas remain valid after adding
free operations.

### New case

If

$$
\Gamma,x:A\vdash V:P_i,
$$

then value substitution gives

$$
\Gamma\vdash V[W/x]:P_i,
$$

and `T-Free` yields

$$
\Gamma\vdash
\mathsf{op}_{\Delta,i}(V[W/x]):R_i!\Delta.
$$

No continuation substitution case is needed in source syntax.

### Theorem II.2 — internal preservation

If $M:A!e$ and $M\to M'$, then $M':A!e$.  All principal reductions are old
Chapter-I rules; the only new form is inert until captured by a future handler.
Context preservation follows from ordered multiplication.

## 2. Effect-aware progress

### Theorem II.3 — extended decomposition

A closed well-typed computation has exactly one selected evaluation form: it
returns, has a uniquely located internal redex, exposes a uniquely located base
request, or exposes a free request of the response type declared by its
interface.  A base request may have several responses in $\mathcal K$; this
does not create two evaluation positions.

### Proof

Induction on syntax, reusing Chapter-I canonical forms.  The new operation case
is immediate.  In a sequencing context, unique decomposition of the left term
determines exactly one enclosing case. $\square$

### Corollary II.4 — empty-free-effect safety

If the extended bound contains no free-interface factor and weakening cannot
remove free factors, evaluation cannot expose a free request.

This is a may-effect safety result.  The converse is false: a term typed using
$1\leq\Delta$ may terminate without exposing $\Delta$.

## 3. Old-language operational conservativity

### Theorem II.5

For an old Chapter-I term, the Chapter-II transition relation and observations
coincide with the Chapter-I ones.

### Proof

Old syntax contains no `op` form.  Every internal rule and every base response
kernel is literally reused, while the new free-request case is unreachable.
Induction on the finite response tree gives equality of the structured
observations in $\mathcal K$. $\square$

## 4. Free-extension algebra

### Theorem II.6

If

$$
\mathsf{StrongGradedMonad}(T,E_B)
\land\mathsf{Polynomial}_1(\Sigma)
\land\forall e,A.\ \mu X.\,T_e(A+\Sigma X)\text{ exists},
$$

then

$$
\mathsf{StrongGradedMonad}(\mathsf F_\Sigma(T),\widehat E)
\land\mathsf{CoherentWeakening}(\tau^{\mathsf F})
\land\mathsf{MonadMorphism}(j)
\land\mathsf{FreeGenerators}(\mathsf{op}^{\mathsf F}).
$$

### Proof sketch

Initiality defines bind as the unique algebra morphism extending a return
substitution.  The left unit, right unit and associativity equations are proved
by showing both sides are algebra morphisms with the same action on returns,
base structure and free generators.  Uniqueness makes them equal.  Strength
and weakening are lifted by the same recursion and inherit coherence from
$T$. $\square$

## 5. Denotational conservativity

### Theorem II.7

For every old typed term,

$$
\llbracket M\rrbracket_{\mathsf F}
=j\circ\llbracket M\rrbracket_T.
$$

### Proof

Induction on typing.  Return uses preservation of $\eta$ by $j$; `let` uses
preservation of graded bind; primitive operations use the definition of the
base lift; branching uses naturality; subeffecting uses weakening coherence.
$\square$

## 6. Operational/denotational correspondence

Extend the base observation domain with

$$
\mathsf{freeReq}_{\Delta,i}(p,k).
$$

The observation records a free request extensionally through its typed
response continuation.  For first-order ground examples this may be tested by
supplying every possible finite response and comparing the resulting base
observations.

### Theorem II.8 — finite adequacy lifting

Assume

$$
\mathsf{BaseCert}(L_B,E_B,\mathcal K,T,\mathsf{obs}_B)
\land\mathsf{WellFounded}(\mathsf F_\Sigma(T))
\land\mathsf{ConstructorSeparated}(\mathsf{observe}_{\mathsf F}).
$$

Then for every closed recursion-free Chapter-II computation:

1. a return is reflected by the return branch of its denotation;
2. a terminal base outcome is reflected by the outer base semantics;
3. an exposed free request is reflected by the corresponding free node;
4. related responses lead to related continuation observations.

### Proof sketch

Induct on the finite operational/denotational operation tree.  Base segments use
the Chapter-I certificate; the free case uses constructor separation and the
induction hypothesis pointwise on responses.  Termination ensures that no
coinductive argument is required. $\square$

## 7. Lifting morphisms and relations

If a base graded monad morphism

$$
q:T\Rightarrow U
$$

preserves primitive interpretations, strength and weakening, initiality gives
a unique lifted morphism

$$
\mathsf F_\Sigma(q):
\mathsf F_\Sigma(T)\Rightarrow\mathsf F_\Sigma(U)
$$

acting by $q$ on base layers and identically on free generators.

Likewise, a bind-compatible base logical relation lifts structurally through
returns, base layers and free nodes.  The free-node clause relates equal
operation tags, related parameters and pointwise-related continuations.

## 8. Chapter-II structure-preservation theorem

### Formal definition of `FreeCert`

For an extension $\widehat L=L_B+\Sigma$ with effect algebra $\widehat E$
and carrier $\mathsf F=\mathsf F_\Sigma(T)$, define

$$
\begin{aligned}
\mathsf{FreeCert}(\widehat L,\widehat E,\mathcal K,\mathsf F)
:=\{\;&
\mathsf{subst}_{\mathsf F},\mathsf{pres}_{\mathsf F},
\mathsf{dec}_{\mathsf F},\mathsf{effsafe}_{\mathsf F},
\mathsf{opcons},\\
&\eta^{\mathsf F},\mu^{\mathsf F},\mathsf{st}^{\mathsf F},
\tau^{\mathsf F},\mathsf{op}^{\mathsf F},j,\\
&\mathsf{monadlaw}_{\mathsf F},\mathsf{embedlaw},
\mathsf{liftMor},\mathsf{liftRel},
\mathsf{adequate}_{\mathsf F}\;\}.
\end{aligned}
\tag{FreeCert}
$$

The new operational fields are

$$
\begin{aligned}
\mathsf{dec}_{\mathsf F}:\quad
&\vdash M:A!e\Rightarrow
 \mathsf{Ret}(M)\mathbin{\dot\vee}\mathsf{Redex}(M)
 \mathbin{\dot\vee}\mathsf{BaseReq}(M)
 \mathbin{\dot\vee}\mathsf{FreeReq}_\Sigma(M),\\
\mathsf{opcons}:\quad
&M\in L_B\Rightarrow
 \mathsf{step}_{\widehat L}(M)=\mathsf{step}_{L_B}(M)
 \in\mathcal K(\mathsf{Conf}+\mathsf{Out}_B),\\
\mathsf{effsafe}_{\mathsf F}:\quad
&\vdash M:A!e\land
 M\to^*\mathcal E[\mathsf{op}_{\Delta,i}(V)]\\
&\hspace{28mm}\Rightarrow
 \exists p,q.\ p\cdot\Delta\cdot q\leq e.
\end{aligned}
$$

The semantic operations have types

$$
\eta_A^{\mathsf F}:A\to\mathsf F_1A,
\quad
\mu_{e,f,A}^{\mathsf F}:\mathsf F_e\mathsf F_fA
\to\mathsf F_{e\cdot f}A,
\quad
j_{e,A}:T_eA\to\mathsf F_eA,
$$

$$
\mathsf{op}^{\mathsf F}_{\Delta,i,e}:
P_i\times(R_i\to\mathsf F_eA)
\to\mathsf F_{\Delta\cdot e}A,
\qquad
\tau^{\mathsf F}_{e,f,A}:\mathsf F_eA\to\mathsf F_fA\ (e\leq f),
$$

with the graded monad/strength/weakening equations and

$$
j\circ\eta^T=\eta^{\mathsf F},
\qquad
j(m\mathbin{\gg=_T}f)
=j(m)\mathbin{\gg=_{\mathsf F}}(j\circ f),
\qquad
j\circ\tau^T=\tau^{\mathsf F}\circ j.
\tag{Embed}
$$

`liftMor` and `liftRel` have the quantified forms

$$
\begin{aligned}
&q:T\Rightarrow U\text{ compatible}
 \Rightarrow\exists!\widehat q:\mathsf F_\Sigma(T)
 \Rightarrow\mathsf F_\Sigma(U),\\
&R\text{ bind/primitive-compatible}
 \Rightarrow\exists\widehat R\text{ closed under return, base layers,
 and free nodes}.
\end{aligned}
$$

Finally, for every closed ground $M$,

$$
\mathsf{adequate}_{\mathsf F}:\quad
\mathsf{run}_{\mathcal K,\mathsf F}(M)
=\mathsf{observe}_{\mathsf F}(\llbracket M\rrbracket),
$$

where $o$ ranges over separated returns, base outcomes and free requests.

### Theorem II.9 — Free extension certificate

Let $P=(L_B,E_B,\mathcal K,T,\mathsf{obs}_B)$ and let $\Sigma$ be disjoint from the base
signature.  The theorem has the explicit form

$$
\begin{aligned}
&\mathsf{BaseCert}(L_B,E_B,\mathcal K,T,\mathsf{obs}_B)\\
&\land\ \mathsf{Polynomial}_1(\Sigma)
\land\ \mathsf{Disjoint}(\Sigma,\Sigma_B)\\
&\land\ \forall e,A.\quad
 \mu X.\,T_e(A+\Sigma X)\text{ exists and is finite/well-founded}\\
&\land\ \mathsf{NoErase}_\Sigma(\leq_{\widehat E})
\land\ \mathsf{Separate}_{\mathsf{obs}}
\quad\Longrightarrow\\[1mm]
&\hspace{18mm}
\mathsf{FreeCert}
(L_B+\Sigma,\widehat E,\mathcal K,\mathsf F_\Sigma(T)).
\end{aligned}
\tag{Free-Transport}
$$

### Boundary

The constructor inductions and initiality arguments are expanded in
[Chapter II — detailed free-extension proofs](chapter-2-proof-details-v5.md).

`FreeCert` does not yet define a handler, eliminate $\Delta$, support general
recursion, or prove that an effect bound is exact.  Those are genuinely later
chapters.  In particular, $1\leq\Delta$ intentionally permits a term annotated
with $\Delta$ to return without performing it.
