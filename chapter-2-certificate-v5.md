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

Assume that $T$ is a strong graded monad, $\Sigma$ is a first-order
polynomial signature, and the indexed layer construction has both its initial
algebras and the coherent base action described in
[Grade-indexed free carrier](grade-indexed-free-carrier-v5.md).  Then

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
\mathsf{BaseSafetyCert}(L_B,E_B,\mathcal K)
\land\mathsf{BaseModelCert}(L_B,E_B,T)
\land\mathsf{BaseAdequacyCert}
(L_B,\mathcal K,T,\mathsf{obs}_B,\mathsf{observe}_T)
\land\mathsf{FiniteResponseCert}(\mathcal K)
\land\mathsf{CarrierCert}(\mathsf F_\Sigma(T))
\land\mathsf{MonadExtCert}(\mathsf F_\Sigma(T),\mathsf{baseAct})
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

The added carrier and monadic premises ensure that the denotation of every
source `let` is actually defined. Initial algebras alone provide constructors
but not the extended bind used in this theorem. The full separation is in the
[assumption dependency audit](assumption-dependency-audit-v5.md).

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

Likewise, a compatible graded base relator

$$
\overline{T,U}_b(R)\subseteq T_bX\times U_bY
$$

has a **structural lifting** $\mathsf{Str}_\Sigma(R)$ through returns, related
base layers and free nodes. The relator is applied to the recursively generated
payload relation and must commute with the two `baseAct` maps. The free-node
clause relates equal operation tags, related parameters and pointwise-related
continuations. This is distinct from the observational graded TT-lifting used
for adequacy.

## 8. Chapter-II structure-preservation theorem

### Definition II.1 — layered Chapter-II certificates

For $\widehat L=L_B+\Sigma$ define the following records.

1. $\mathsf{OpFreeCert}(\widehat L)$ contains extended substitution and
   preservation, four-way return/redex/base/free-request decomposition, and
   literal old-language operational conservativity.
2. $\mathsf{EffectSafetyCert}(\widehat L,\widehat E)$ contains the factorization
   property `effsafe`: every exposed $\Delta$ request occurs at some typed
   position $p\Delta q\le e$. It does not require no-erasure.
3. $\mathsf{EmptyFreeCert}(\widehat E)$ contains the no-erasure implication

   $$
   \neg\mathsf{contains}_\Sigma(e)
   \Longrightarrow
   \neg\exists p,q,\Delta\in\Sigma.\ p\Delta q\le e.
   \tag{No-Erase}
   $$

4. $\mathsf{CarrierCert}(T,\Sigma,\mathsf F)$ contains the indexed Lambek
   isomorphisms $\alpha_A:\mathcal H_A(\mathsf F A)\cong\mathsf F A$, their
   naturality in $A$, coherent weakening, and the return/base/free
   constructors.
5. $\mathsf{MonadExtCert}(T,\mathsf F,\mathsf{act})$ contains `Act-Unit`,
   `Act-Mult`, weakening, strength and free-node coherence, together with the
   induced graded monad laws and monadic base embedding.
6. $\mathsf{FunctorCert}(\mathsf F)$ states that every structure- and
   action-compatible base morphism has a unique lifted strong graded monad
   morphism and that these lifts preserve identity and composition.
7. $\mathsf{RelCert}(\mathsf F)$ takes a compatible graded relator as input,
   includes `Rel-Act`, constructs $\mathsf{Str}_\Sigma$, and supplies bind
   closure and the graph law for graph-preserving relators.
8. $\mathsf{FiniteAdequacyCert}(\widehat L,\mathcal K,\mathsf F)$ contains the
   canonical pole, pole closure, the finite fundamental lemma and equality of
   closed ground observations.

The record names used in the dependency audit are therefore definitions, not
informal labels.

### Definition II.2 — bundled `FreeCert`

For an extension $\widehat L=L_B+\Sigma$ with effect algebra $\widehat E$
and carrier $\mathsf F=\mathsf F_\Sigma(T)$, we say that

$$
\mathsf{FreeCert}(\widehat L,\widehat E,\mathcal K,\mathsf F)
$$

holds when the following conditions are satisfied.

1. **Extended operational safety.** Substitution and preservation continue to
   hold; decomposition gains the free-request case; exposed requests respect
   their bounds.
2. **Old-language conservativity.** The extended machine has exactly the old
   response kernel on old terms.
3. **Free graded semantics.** $\mathsf F$ has graded return, multiplication,
   strength, weakening and free generators, with the expected laws.
4. **Base embedding.** The canonical $j:T\to\mathsf F$ preserves return,
   bind, strength and weakening.
5. **Functorial and relational transport.** Compatible morphisms lift;
   compatible relations have a structural lifting satisfying the graph law;
   graded TT relations transport through a closed pole.
6. **Finite adequacy.** Closed ground observations agree in $\mathcal K$.

Equivalently, `FreeCert` is the conjunction of the eight records above. It is
retained for the end-to-end theorem and concrete examples; intermediate
theorems use the smallest appropriate record.

Conditions (1) and (2) are formally:

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

Conditions (3) and (4) require the following operations and equations:

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

Condition (5) has the quantified forms

$$
\begin{aligned}
&q:T\Rightarrow U\text{ compatible}
 \Rightarrow\exists!\widehat q:\mathsf F_\Sigma(T)
 \Rightarrow\mathsf F_\Sigma(U),\\
&\overline{T,U}\text{ a compatible graded relator}
 \Rightarrow\exists\mathsf{Str}_\Sigma(R)\text{ closed under return, related
 base layers, free nodes and bind},\\
&\mathsf{Str}_\Sigma(\overline q)
 =\operatorname{Graph}(\mathsf F_\Sigma q),\\
&\mathsf{TTCert}(T,U,\mathcal O)
 \land\mathsf{PoleClosed}_\Sigma(\mathcal O^\Sigma)\\
&\hspace{18mm}\Rightarrow
 \mathsf{Str}_\Sigma(V^{\top\top})
 \subseteq V^{\top_\Sigma\top_\Sigma}.
\end{aligned}
$$

Here compatibility of $q$ includes the
[base-action square](base-action-law-v5.md), in addition to preservation of
the old graded monad operations.

Compatibility of $\overline{T,U}$ includes monotonicity and naturality in the
payload relation, return/bind/strength/weakening/primitive closure and

$$
u\mathrel{\overline{T,U}_b(\mathsf{Str}_{\Sigma,d}(R))}v
\Rightarrow
\mathsf{act}^T_{b,d}(u)
\mathrel{\mathsf{Str}_{\Sigma,bd}(R)}
\mathsf{act}^U_{b,d}(v).
\tag{Free-Rel-Act}
$$

Thus `graphLaw` is an equality only for the least structural lifting.
`ttTransport` maps it into the generally larger observational closure.  The
grade-indexed pole and `TTCert` are defined in
[Graded TT-lifting](graded-tt-lifting-v5.md).

Condition (6), for every closed ground $M$, is

$$
\mathsf{adequate}_{\mathsf F}:\quad
\mathsf{run}_{\mathcal K,\mathsf F}(M)
=\mathsf{observe}_{\mathsf F}(\llbracket M\rrbracket),
$$

where $o$ ranges over separated returns, base outcomes and free requests.

### Theorem II.9 — layered free-extension certificates

Assume the following premises, each only where cited below.

1. $\mathsf{BaseSafetyCert}(L_B,E_B,\mathcal K)$;
2. $\mathsf{BaseModelCert}(L_B,E_B,T)$;
3. $\mathsf{BaseAdequacyCert}
   (L_B,\mathcal K,T,\mathsf{obs}_B,\mathsf{observe}_T)$;
4. $\Sigma$ is a first-order polynomial signature disjoint from the base
   signature;
5. for every $A$, the indexed layer functor $\mathcal H_A$ from
   [the grade-indexed construction](grade-indexed-free-carrier-v5.md) has a
   finite/well-founded initial algebra in $\mathcal C^{\widehat E}$, stable
   under the products required by strength, and its carrier has the coherent
   base action $T_b(\mathsf F_dA)\to\mathsf F_{b\cdot d}A$;
6. the extended effect preorder cannot erase a visible $\Sigma$ factor;
7. $\mathsf{FiniteResponseCert}(\mathcal K)$ holds;
8. the extended observation separates returns, base outcomes and free
   requests.

Then the following conclusions hold in order.

1. Premises 1 and 4 give
   $\mathsf{OpFreeCert}(L_B+\Sigma)$ without using premises 2, 3 and 5--8.
2. The same typing argument gives $\mathsf{EffectSafetyCert}$ without
   no-erasure. Adding premise 6 gives the stronger `EmptyFreeCert` corollary.
3. Premises 2 and 4 and the initial-algebra part of premise 5 give
   $\mathsf{CarrierCert}(T,\Sigma,\mathsf F)$.
4. Adding the base-action part of premise 5 gives
   $\mathsf{MonadExtCert}(T,\mathsf F,\mathsf{act})$.
5. Compatible morphisms and graded relators respectively give
   $\mathsf{FunctorCert}$ and $\mathsf{RelCert}$; neither conclusion uses
   base adequacy, finite responses or constructor separation.
6. Finally, premises 1--5, 7 and 8 give
   $\mathsf{FiniteAdequacyCert}$.

Consequently all premises together yield

$$
\mathsf{FreeCert}
(L_B+\Sigma,\widehat E,\mathcal K,\mathsf F_\Sigma(T))
$$

holds.

### Boundary

The constructor inductions and initiality arguments are expanded in
[Chapter II — detailed free-extension proofs](chapter-2-proof-details-v5.md).

`FreeCert` does not yet define a handler, eliminate $\Delta$, support general
recursion, or prove that an effect bound is exact.  Those are genuinely later
chapters.  In particular, $1\leq\Delta$ intentionally permits a term annotated
with $\Delta$ to return without performing it.
