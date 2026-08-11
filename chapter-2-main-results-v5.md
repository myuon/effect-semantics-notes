# Chapter II — preservation proofs and `FreeExtensionPackage`

:::{admonition} Lean correspondence — `FreeExtensionPackage`
:class: tip
Read this page in three layers: typed source, finite semantic core, and the
conditional general graded theorem. Lean states substitution, preservation,
four-way progress, tree semantics, and adequacy as individual declarations;
there is no source-stage result record. Likewise, the grade-independent core
is [`FreeExtension`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension#doc)
plus separate monad, embedding, relation, shallow-handler, and fold theorems.
`LanguageWriterTree.toFreeExtension` connects the finite source tree to that
generic core and preserves bind. The stronger grade-indexed presentation below
remains a paper abstraction. [Full mapping](review-guide.md#chapter-ii-free-operations).
:::

### Numbered-statement inventory

| statement | review status | correspondence |
|---|---|---|
| Lemma II.1–Theorem II.3, substitution/preservation/progress | Lean checked, including exact four-way statement | [`LanguageStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc), [`progressClosed_fourWayExactlyOne`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed_fourWayExactlyOne#doc) |
| Boundary II.4, empty-free-effect safety | false without non-erasure; repaired theorem Lean checked | [`not_exposed_of_interface_absent`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.TypedLanguageFreeRequest.not_exposed_of_interface_absent#doc) |
| Theorem II.5, old-language operational conservativity | Lean checked for current `LanguageComp` | [`FinLanguageSteps.baseOnly_boundary_is_base`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FinLanguageSteps.baseOnly_boundary_is_base#doc) |
| Theorem II.6, free-extension algebra | Lean checked as separate laws | [`genericFreeMonad`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericFreeMonad#doc), [`embedBase_bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.embedBase_bind#doc), [`Rel.bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.bind#doc) |
| Theorem II.7, finite denotational conservativity | Lean checked, with source-tree bridge | [`eraseFree_embedBase`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.eraseFree_embedBase#doc), [`toFreeExtension_bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageWriterTree.toFreeExtension_bind#doc) |
| Theorem II.8, finite model-comparison lifting | Lean checked | [`GenericExtensionAlgebra.ModelComparison.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.ModelComparison.lift#doc) |
| Definition II.1–II.2 and Theorem II.9, `FreeExtensionPackage` | readable grade-indexed abstraction; finite components Lean checked separately | [`FreeExtension`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension#doc) |

## Status

**Conditional paper theorem.**  This page proves the recursion-free free
extension properties relative to the explicit `BasePackage` and initial-algebra
hypotheses.

## 1. Substitution and preservation

### Lemma II.1 `[C2-MAIN.1.1]` — substitution [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.subst_preserved#doc)

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

### Theorem II.2 `[C2-MAIN.1.2]` — internal preservation [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc)

If $M:A!e$ and $M\to M'$, then $M':A!e$.  All principal reductions are old
Chapter-I rules; the only new form is inert until captured by a future handler.
Context preservation follows from ordered multiplication.

## 2. Effect-aware progress

### Theorem II.3 `[C2-MAIN.2.1]` — extended decomposition [[Lean: exact four-way theorem]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed_fourWayExactlyOne#doc)

A closed well-typed computation has exactly one selected evaluation form: it
returns, has a uniquely located internal redex, exposes a uniquely located base
request, or exposes a free request of the response type declared by its
interface. Effectful branching may live in the operational monad $S$; this
does not create two evaluation positions.

### Proof

Induction on syntax, reusing Chapter-I canonical forms.  The new operation case
is immediate.  In a sequencing context, unique decomposition of the left term
determines exactly one enclosing case. $\square$

### Boundary II.4 `[C2-MAIN.2.2]` — empty-free-effect safety [[Lean: counterexample]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.empty_free_effect_safety_counterexample#doc) [[Lean: repaired theorem]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.TypedLanguageFreeRequest.not_exposed_of_interface_absent#doc)

The unconditional statement is false for the current effect algebra:
sequential composition with `bottom` erases every prefix.  Lean checks a
closed typed term whose annotation is `bottom` but whose first boundary is a
free request.  The repaired theorem assumes that every continuation frame is
**non-erasing**, meaning its suffix language contains the empty trace.  Under
that premise, absence of the selected interface from every trace in the final
bound implies that evaluation cannot expose the request.

This repaired statement is a may-effect safety result.  The converse is false: a term typed using
$1\leq\Delta$ may terminate without exposing $\Delta$.

## 3. Old-language operational conservativity

### Theorem II.5 `[C2-MAIN.3.1]` — old-language operational conservativity [[Lean: one step]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preservesBaseOnly#doc) [[Lean: finite run]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FinLanguageSteps.baseOnly_boundary_is_base#doc)

For an old Chapter-I term, the Chapter-II transition relation and observations
coincide with the Chapter-I ones.

### Proof

Base-only syntax contains no `freeOp` form. Lean proves closure under renaming
and substitution, then preservation by every `LanguageStep`. Induction over
`FinLanguageSteps` shows that any boundary reached from such a term has kind
`base`; hence the new free-request case is unreachable. Equality of a chosen
base interpreter is a separate, model-specific consequence rather than part
of this operational theorem.
$\square$

## 4. Free-extension algebra

### Theorem II.6 `[C2-MAIN.4.1]` — free-extension algebra [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericFreeMonad#doc)

Assume that the strong graded free monad transformer
$\widehat T=\operatorname{FreeT}_\Sigma(T)$ exists in the sense of
[FreeT existence](graded-freet-existence-v1.md). Then

$$
\mathsf{StrongGradedMonad}(\mathsf F_\Sigma(T),\widehat E)
\land\mathsf{CoherentWeakening}(\tau^{\mathsf F})
\land\mathsf{MonadMorphism}(j)
\land\mathsf{FreeGenerators}(\mathsf{op}^{\mathsf F}).
$$

### Proof sketch

For the ordinary ungraded FreeT, fold/unfold derives the base action as
$\mathsf{roll}\circ\mu^T\circ T(\mathsf{out})$. A
`StrongGradedFreeT` package includes the corresponding typed action and its
laws; establishing that package must construct them. Initiality defines bind as
the unique algebra morphism extending a return substitution. The left unit,
right unit and associativity equations are proved
by showing both sides are algebra morphisms with the same action on returns,
base structure and free generators.  Uniqueness makes them equal.  Strength
and weakening are lifted by the same recursion and inherit coherence from
$T$. $\square$

## 5. Denotational conservativity

### Theorem II.7 `[C2-MAIN.5.1]` — finite denotational conservativity [[Lean: base retraction]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.eraseFree_embedBase#doc) [[Lean: source-tree bridge]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageWriterTree.toFreeExtension_bind#doc)

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

Extend both models by the same free signature:
$\widehat S=\mathsf F_\Sigma(S)$ and
$\widehat T=\mathsf F_\Sigma(T)$.

### Theorem II.8 `[C2-MAIN.6.1]` — finite model-comparison lifting [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.ModelComparison.lift#doc)

Assume

$$
\mathsf{BasePackage}(L_B,E_B,S,T,q)
\land\mathsf{StrongGradedFreeT}(S,\Sigma,\widehat S)
\land\mathsf{StrongGradedFreeT}(T,\Sigma,\widehat T).
$$

Then $q$ lifts uniquely to
$\widehat q:\widehat T\Rightarrow\widehat S$, and every closed
recursion-free Chapter-II computation satisfies

$$
\widehat q(\llbracket M\rrbracket_{\widehat T})
=\llbracket M\rrbracket_{\widehat S}.
$$

### Proof sketch

Induct on the finite operation tree. Base segments use primitive commutation;
the free case maps the request and its continuations recursively. Initiality
gives uniqueness. A subsequent observation/TT theorem may additionally use
constructor separation and the induction hypothesis pointwise on responses.
Termination ensures that no coinductive argument is required. $\square$

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
payload relation. Closure under the two chosen `baseAct` maps is the
`Rel-Act` premise; unlike the graph of a canonical morphism, it does not
follow for an arbitrary relation merely from the FreeT fold equation. The free-node
clause relates equal operation tags, related parameters and pointwise-related
continuations. This is distinct from the observational graded TT-lifting used
for adequacy.

## 8. Chapter-II structure-preservation theorem

The matching source/tree commutation is checked by
[`ProducesLanguageWriterTree.answerWith`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.answerWith#doc);
its operational/tree adequacy component is
[`language_writer_operational_tree_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.language_writer_operational_tree_adequacy#doc).

### Definition II.1 `[C2-MAIN.8.1]` — layered Chapter-II packages [[Lean: source stage]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed_fourWayExactlyOne#doc) [[Lean: semantic core]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension#doc)

For $\widehat L=L_B+\Sigma$, the paper proof is factored into the following
eight package interfaces. These names describe the dependency boundary;
they are not eight same-named Lean structures.

1. $\mathsf{OpFreeExtensionPackage}(\widehat L)$ contains extended substitution and
   preservation, four-way return/redex/base/free-request decomposition, and
   literal old-language operational conservativity.
2. $\mathsf{EffectSafety}(\widehat L,\widehat E)$ contains the factorization
   property `effsafe`: every exposed $\Delta$ request occurs at some typed
   position $p\Delta q\le e$. It does not require no-erasure.
3. $\mathsf{NoErasureCondition}(\widehat E)$ contains the no-erasure implication

   $$
   \neg\mathsf{contains}_\Sigma(e)
   \Longrightarrow
   \neg\exists p,q,\Delta\in\Sigma.\ p\Delta q\le e.
   \tag{No-Erase}
   $$

4. $\mathsf{CarrierStructure}(T,\Sigma,\mathsf F)$ contains the indexed Lambek
   isomorphisms $\alpha_A:\mathcal H_A(\mathsf F A)\cong\mathsf F A$, their
   naturality in $A$, coherent weakening, and the return/base/free
   constructors.
5. $\mathsf{MonadExtensionLaws}(T,\mathsf F,\mathsf{act})$ contains `Act-Unit`,
   `Act-Mult`, weakening, strength and free-node coherence, together with the
   induced graded monad laws and monadic base embedding.
6. $\mathsf{FunctorialityLaws}(\mathsf F)$ states that every structure- and
   action-compatible base morphism has a unique lifted strong graded monad
   morphism and that these lifts preserve identity and composition.
7. $\mathsf{RelationLaws}(\mathsf F)$ takes a compatible graded relator as input,
   includes `Rel-Act`, constructs $\mathsf{Str}_\Sigma$, and supplies bind
   closure and the graph law for graph-preserving relators.
8. $\mathsf{FiniteAdequacyAssumptions}(\widehat L,\mathcal K,\mathsf F)$ contains the
   canonical pole, pole closure, the finite fundamental lemma and equality of
   closed ground observations.

Lean exposes the checked finite portions as individual source and
free-extension theorems, plus narrowly scoped model-comparison assumptions.
The grade-indexed fields in items 4–8 remain
requirements of the paper `StrongGradedFreeT` presentation.

### Definition II.2 `[C2-MAIN.8.2]` — bundled `FreeExtensionPackage` [Readable grade-indexed abstraction]

For an extension $\widehat L=L_B+\Sigma$ with effect algebra $\widehat E$
and denotational carrier
$\widehat T:=\mathsf F_\Sigma(T)$, we say that

$$
\mathsf{FreeExtensionPackage}(\widehat L,\widehat E,\mathcal K,\widehat T)
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

At paper level, `FreeExtensionPackage` abbreviates the conjunction of the eight interfaces
above. It is not currently a same-named Lean record; mechanized intermediate
theorems use the smaller source and finite-semantic records just listed.

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
\eta_A^{\widehat T}:A\to\widehat T_1A,
\quad
\mu_{e,f,A}^{\widehat T}:\widehat T_e\widehat T_fA
\to\widehat T_{e\cdot f}A,
\quad
j_{e,A}:T_eA\to\widehat T_eA,
$$

$$
\mathsf{op}^{\widehat T}_{\Delta,i,e}:
P_i\times(R_i\to\widehat T_eA)
\to\widehat T_{\Delta\cdot e}A,
\qquad
\tau^{\widehat T}_{e,f,A}:\widehat T_eA\to\widehat T_fA\ (e\leq f),
$$

with the graded monad/strength/weakening equations and

$$
j\circ\eta^T=\eta^{\widehat T},
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
&\mathsf{TTClosure}(T,U,\mathcal O)
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
grade-indexed pole and `TTClosure` are defined in
[Graded TT-lifting](graded-tt-lifting-v5.md).

Condition (6), for every closed ground $M$, is

$$
\mathsf{adequate}_{\mathsf F}:\quad
\mathsf{run}_{\mathcal K,\mathsf F}(M)
=\mathsf{observe}_{\mathsf F}(\llbracket M\rrbracket),
$$

where $o$ ranges over separated returns, base outcomes and free requests.

### Theorem II.9 `[C2-MAIN.8.3]` — layered free-extension packages [[Lean: source theorem]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc) [[Lean: generic theorem]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericFreeMonad#doc)

Assume the following premises, each only where cited below.

1. $\mathsf{BasePackage}(L_B,E_B,S,T,q)$;
2. $\Sigma$ is a first-order polynomial signature disjoint from the base
   signature;
3. $\mathsf{StrongGradedFreeT}(T,\Sigma,\widehat T)$ and
   $\mathsf{StrongGradedFreeT}(S,\Sigma,\widehat S)$ hold; accessible
   carrier conditions and concrete structural constructions are listed in
   [FreeT existence](graded-freet-existence-v1.md);
4. the extended effect preorder cannot erase a visible $\Sigma$ factor;
5. any optional finite TT observation theorem supplies its own branching,
   separation, and pole-closure hypotheses.

Then the following conclusions hold in order.

1. Premises 1 and 2 give $\mathsf{OpFreeExtensionPackage}(L_B+\Sigma)$ independently of
   the semantic FreeT premise.
2. The same typing argument gives $\mathsf{EffectSafety}$; adding premise
   4 gives the stronger `NoErasureCondition` corollary.
3. Premise 3 gives both extended strong graded monads, their base embeddings,
   free generators, and the chosen coherent actions.
4. The base comparison $q$ lifts functorially to
   $\widehat q:\widehat T\Rightarrow\widehat S$.
5. Compatible graded relators lift in parallel.
6. Adding premise 5 yields the selected finite TT/fundamental and observation
   conclusions.

Consequently all premises together yield

$$
\mathsf{FreeExtensionPackage}
(L_B+\Sigma,\widehat E,\widehat S,\widehat T,\widehat q)
$$

holds.

The two linked Lean theorems check the source-language and ungraded generic
structural layers exactly. The strong graded FreeT existence theorem remains a
paper-level premise; no unchecked bridge equating the Lean finite tree carrier
with the general categorical construction is claimed.

### Boundary

The constructor inductions and initiality arguments are expanded in
[Chapter II — detailed free-extension proofs](chapter-2-proof-details-v5.md).

`FreeExtensionPackage` does not yet define a handler, eliminate $\Delta$, support general
recursion, or prove that an effect bound is exact.  Those are genuinely later
chapters.  In particular, $1\leq\Delta$ intentionally permits a term annotated
with $\Delta$ to return without performing it.
