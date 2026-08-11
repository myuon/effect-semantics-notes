# Chapter III — shallow-handler proofs and `ShallowHandlerPackage`

:::{admonition} Lean correspondence — `ShallowHandlerPackage`
:class: tip
The source-language results are separate Lean theorems: handler preservation
is [`LanguageShallowStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageShallowStep.preserve#doc),
progress is [`HasLanguageHandlerState.progressClosed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageHandlerState.progressClosed#doc),
and structural/TT preservation is stated directly on `LanguageWriterTree.Rel`.
No stage record collects these results. [Full mapping](review-guide.md#chapter-iii-shallow-handlers).
:::

### Numbered-statement inventory

| statement | review status | correspondence |
|---|---|---|
| Lemma III.1, continuation typing | Lean checked component | [`LanguageFreeRequest.openResume_subst0`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageFreeRequest.openResume_subst0#doc) |
| Theorem III.2, handler preservation | Lean checked directly | [`LanguageShallowStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageShallowStep.preserve#doc) |
| Theorem III.3, affine effect transformation | Lean checked component | [`EffectLanguage.handleWith_mono`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.EffectLanguage.handleWith_mono#doc) |
| Theorem III.4, operational/denotational commutation | Lean checked directly | [`ProducesLanguageWriterTree.answerWith`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.answerWith#doc) |
| Theorem III.5, adequacy preservation | Model-comparison component Lean checked; observation/handler theorem remains conditional | [`GenericExtensionAlgebra.Morphism.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.Morphism.lift#doc) |
| Definition III.1–III.3 and Theorem III.6 | readable paper decomposition; Lean components are separate | [`HasLanguageHandlerState.progressClosed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageHandlerState.progressClosed#doc) |

## Status

**Conditional paper theorem.**  The affine fragment has a derived effect
transformer.  The general fragment is conditional on a supplied handler-effect
package.

## 1. Typing preservation

### Lemma III.1 `[C3-MAIN.1.1]` — continuation typing [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageFreeRequest.openResume_subst0#doc)

If

$$
\mathcal E[\mathsf{op}_{\Delta,i}(V)]:A!e_{\mathsf{in}},
$$

then residual-context typing gives an effect $e_k$ such that

$$
k=\lambda r.\mathcal E[\mathsf{return}\,r]
:
R_i\xrightarrow{e_k}A.
$$

The ordered input bound contains the primitive grade $\Delta$ before $e_k$,
up to the declared weakening.

### Theorem III.2 `[C3-MAIN.1.2]` — handler preservation [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageShallowStep.preserve#doc)

If

$$
\mathsf{OpFreeExtensionPackage}(L_B+\Sigma)
\land\mathsf{HandlerTyping}(\Delta,J,h,\Phi_h)
\land\Gamma\vdash M:A!e,
$$

then

$$
\Gamma\vdash
\mathsf{shallow}_\Delta M\ \mathsf{with}\ h
:C!\Phi_h(e),
$$

and every handler reduction preserves this type and bound.

### Proof

`SH-Ret` uses value substitution.  `SH-Match` uses parameter substitution and
Lemma III.1 for $k$.  `SH-Forward` uses the free-request typing rule and the
structural handler-typing induction for its rewrapped continuation.  Reductions
inside the scrutinee use Chapter-II preservation. $\square$

## 2. Affine effect theorem

### Theorem III.3 `[C3-MAIN.2.1]` — affine effect transformation [[Lean: anchored theorem]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.EffectLanguage.anchored_replacement_le_handleWith_of_bounds#doc) [[Lean: monotonicity]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.EffectLanguage.handleWith_mono#doc) [[Boundary: naive word transformer]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.TypedWriterTree.replaceFirst_not_monotone#doc)

If $b$ is $\Delta$-free and

$$
\mathsf{OpFreeExtensionPackage}(L_B+\Sigma)
\land\mathsf{EffectSafety}(L_B+\Sigma,\widehat E)
\land\mathsf{AffineHandlerLaws}(\Delta,h,e')
\land\Gamma\vdash M:A!(b\cdot\Delta\cdot e),
$$

then

$$
\Gamma\vdash
\mathsf{shallow}_\Delta M\ \mathsf{with}\ h
:A!(b\cdot e'\cdot e).
$$

### Proof

On a matching request, residual-context typing identifies the bare tail at
$e$; response sequencing gives $e'\cdot e$, and the already evaluated prefix
contributes $b$.  If the optional request is absent, the computation follows a
path bounded by $b\cdot e$, and

$$
b\cdot e\leq b\cdot e'\cdot e
$$

follows from $1\leq e'$ and monotonicity.  The return rule is identity. $\square$

This theorem is an upper-bound theorem, not an assertion that every run reaches
$\Delta$. Lean checks the sharp theorem for the displayed anchored
factorization and obtains its weakened language-bound form by monotonicity. It
separately checks that raw `replaceFirst` on arbitrary upper words is not
monotone; that stronger formulation is therefore not claimed.

## 3. Operational/denotational commutation

### Theorem III.4 `[C3-MAIN.3.1]` — operational/denotational commutation [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.answerWith#doc)

If

$$
\mathsf{CarrierStructure}(T,\Sigma,\mathsf F_\Sigma(T))
\land\mathsf{MonadExtensionLaws}(T,\mathsf F_\Sigma(T),\mathsf{act})
\land\mathsf{DenotationalModel}(L_B,E_B,T)
\land\mathsf{HandlerTyping}(\Delta,J,h,\Phi_h),
$$

then, for every closed recursion-free handled computation,

$$
\llbracket
\mathsf{shallow}_\Delta M\ \mathsf{with}\ h
\rrbracket
=
\mathsf{sh}_{\Delta,h}(\llbracket M\rrbracket).
$$

### Proof sketch

Induct on the finite outer base/free structure supplied by `CarrierStructure`.

- return uses the return equation;
- an internal/base step uses functoriality and Chapter-II soundness;
- a matching request uses semantic substitution for $p$ and $k$;
- a nonmatching request rebuilds the same constructor and uses the induction
  hypothesis pointwise on its rewrapped continuation.

The matching case deliberately does not apply the induction hypothesis to its
bare continuation.  This distinguishes shallow from deep handling.

## 4. Adequacy preservation

### Theorem III.5 `[C3-MAIN.4.1]` — adequacy preservation [[Lean: model-comparison component]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericExtensionAlgebra.Morphism.lift#doc)

Assume

$$
\begin{aligned}
&\mathsf{FiniteAdequacyAssumptions}(L_B+\Sigma,\mathcal K,\mathsf F_\Sigma(T))\\
&\land\mathsf{HandlerTyping}(\Delta,J,h,\Phi_h)
\land\mathsf{TTClosure}(S,T,\mathcal O)
\land\mathsf{HandlerTTClosure}(h).
\end{aligned}
$$

Here `TTClause` means, for every operation clause,

$$
p_S\,V_P\,p_T
\land k_S\mathrel{V_R^{\top}}k_T
\Rightarrow
h_S(p_S,k_S)\mathrel{V_C^{\top\top}}h_T(p_T,k_T),
$$

with the analogous value relation for return clauses.

Then ground adequacy is preserved by the shallow handler:
operational returns, base outcomes, matching replacements and forwarded
requests agree with the structural shallow denotation.

The linked Lean theorem checks the fold-naturality/model-comparison component.
The observation-specific TT and handler conclusion remains conditional on the
displayed `FiniteAdequacyAssumptions`, `TTClosure`, and `HandlerTTClosure` premises.

### Proof

Combine Theorem III.4 with Chapter-II finite adequacy.  Ordinary clause
computations use the graded TT fundamental lemma; matching clauses use
`TTClause`; forwarded continuations use orthogonality and pole closure.
`observeReflect` converts the final TT relation into adequacy. $\square$

## 5. Conservativity

Adding the handler syntax does not alter reduction or denotation of terms that
do not use it.  Moreover, the affine identity handler is observationally the
identity on computations whose bound contains no matching $\Delta$, subject to
transparent forwarding.

The latter statement does not say that a general handler with a nontrivial
return clause is identity on old programs.

## 6. Chapter-III structure-preservation theorem

The mechanized matching theorem is
[`ProducesLanguageWriterTree.answerWith`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.answerWith#doc),
while shallow naturality, structural-relation preservation and TT preservation
are separate theorems such as [`LanguageWriterTree.Rel.shallow`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageWriterTree.Rel.shallow#doc).

### Definition III.1 `[C3-MAIN.6.1]` — layered handler packages [[Lean: exact source package]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageHandlerState.progressClosed#doc)

Let $J\subseteq I_\Delta$ be the operations for which $h$ supplies clauses,
and let $\Phi_h:\widehat E\to\widehat E$. We say that
$\mathsf{HandlerTyping}(\Delta,J,h,\Phi_h)$ holds when:

1. **Monotonicity.** $\Phi_h$ respects subeffecting.
2. **Return typing.** The return clause has an effect below $\Phi_h(1)$.
3. **Matching typing.** Every operation clause transforms each admissible
   residual bound below the declared output bound.
4. **Transparent forwarding.** A nonmatching operation is rebuilt and the
   handler remains on its continuation; the effect transformer preserves the
   unhandled prefix and transforms its residual bound.

The handler need not be exhaustive. A request $\mathsf{op}_{\Delta,i}$ with
$i\notin J$ follows the same forwarding rule as a request from another
interface.

Separately:

1. $\mathsf{HandlerStructuralLaws}(h)$ says that return, handled clauses and
   forwarding preserve the structural relation.
2. $\mathsf{HandlerTTClosure}(h)$ says that return and handled clauses satisfy
   `TTClause`, while forwarding preserves the extended pole.
3. $\mathsf{EliminationLaws}(\Delta,J,h,\Phi_h)$ requires $J=I_\Delta$ and
   proves that the selected interface occurrence is absent from the declared
   output position. At interface-level granularity this conclusion is not
   available for a genuinely partial $J$.

The bundled name
$\mathsf{HandlerPackage}(\Delta,J,h,\Phi_h)$ abbreviates the conjunction of the
typing, structural and TT packages. It does **not** include
`EliminationLaws`.

### Mechanized ordered-subsumption boundary

The exact-grade exhaustive tree theorem is now kernel-checked: replacing the
first selected interface in an exact word commutes with the typed structural
shallow fold. It does **not** follow that the same word transformer is
monotone for ordered-subsequence subeffecting. Lean checks the concrete
counterexample

$$
X\Delta\leq\Delta X\Delta,
\qquad
\mathsf{replaceFirst}_{\Delta,R}(X\Delta)=XR,
\qquad
\mathsf{replaceFirst}_{\Delta,R}(\Delta X\Delta)=RX\Delta,
$$

while $XR\not\leq RX\Delta$. Thus `mono_h` is a genuine extra package
condition and cannot be discharged by taking $\Phi_h$ to be naive
first-occurrence replacement. Three sound continuations of the theorem are
now distinguished:

1. retain principal/exact grades for the sharp equation;
2. use a coarser monotone upper envelope after subsumption;
3. enrich the effect domain from a single word to a downward-closed language
   of possible words.

The Lean development also constructs a finite word envelope containing the
replacement of every subword of a fixed upper word. This proves local
existence of a sound coarse bound, but not yet a canonical compositional
transformer.

Writing $\mathsf{grade}(K)\leq d$ for “$K$ type-checks at an effect below
$d$”, these conditions are

$$
\begin{aligned}
\mathsf{mono}_h:&\quad
e\leq f\Rightarrow\Phi_h(e)\leq\Phi_h(f),\\
\mathsf{return}_h:&\quad
\Gamma,x:A\vdash H_{\mathsf{ret}}:C!r
\land r\leq\Phi_h(1),\\
\mathsf{match}_h:&\quad
\forall i\in J,b,e,d.\ b\cdot\Delta\cdot e\leq d\\
&\Rightarrow
\Bigl(
\Gamma,p:P_i,k:R_i\xrightarrow{e}A
\vdash H_i:C!c_i
\land b\cdot c_i\leq\Phi_h(d)
\Bigr),\\
\mathsf{forward}_h:&\quad
(\Gamma'\neq\Delta\lor(\Gamma'=\Delta\land j\notin J))\Rightarrow
\mathsf{sh}_h(\mathsf{op}_{\Gamma',j}(p,k))\\
&\hspace{25mm}=
\mathsf{op}_{\Gamma',j}
(p,\lambda r.\mathsf{sh}_h(k(r))),\\
\mathsf{forwardGrade}_h:&\quad
\forall b,e,d.\ b\cdot\Gamma'\cdot e\le d\\
&\quad\land(\Gamma'\neq\Delta\lor(\Gamma'=\Delta\land j\notin J))\\
&\hspace{25mm}\Rightarrow
b\cdot\Gamma'\cdot\Phi_h(e)\le\Phi_h(d),\\
\mathsf{structuralClause}_h:&\quad
(p,k)\mathrel{\mathsf{Str}_\Delta(R)}(p',k')
\Rightarrow H_i[p,k]\mathrel{\mathsf{Str}_\Delta(R)}h_i(p',k'),\\
\mathsf{TTClause}_h:&\quad
p_S\,V_P\,p_T\land k_S\mathrel{V_R^{\top}}k_T
\Rightarrow
h_S(p_S,k_S)\mathrel{V_C^{\top\top}}h_T(p_T,k_T).
\end{aligned}
$$

### Definition III.2 `[C3-MAIN.6.2]` — `AffineHandlerLaws` [[Lean: source typing structure]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageAffineHandler#doc)

The affine response fragment satisfies
$\mathsf{AffineHandlerLaws}(\Delta,h,e')$ when:

1. $h$ has a clause for every operation in $\Delta$;
2. its return clause is $H_{\mathsf{ret}}=\mathsf{return}\,x$;
3. each response computation has
   $\Gamma,p:P_i\vdash R_i(p):R_i!e'$;
4. each operation clause is
   $H_i\equiv\mathbf{let}\ r\leftarrow R_i(p)\ \mathbf{in}\ k\,r$;
5. $1\leq e'$.

For this fragment, on the domain of grades whose displayed prefix $b$ is
$\Delta$-free,

$$
\Phi_{\Delta,e'}(b\cdot\Delta\cdot e)=b\cdot e'\cdot e.
$$

Thus `AffineHandlerLaws` includes
$\mathsf{EliminationLaws}(\Delta,I_\Delta,h,\Phi_{\Delta,e'})$. A partial
affine family has the same clause calculation but not this interface-level
elimination conclusion.

### Definition III.3 `[C3-MAIN.6.3]` — layered shallow packages [[Lean: exact source package]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageHandlerState.progressClosed#doc)

Define:

1. `ShallowSafety` by preservation, progress and the return/match/forward
   operational boundary equations;
2. `ShallowSemantics` by commutation of direct and structural handling;
3. `ShallowRelationLaws` by preservation of the lifted structural and TT
   relations;
4. `ShallowAdequacyAssumptions` by equality of handled operational and denotational
   observations;
5. `ShallowElimination` by `EliminationLaws` and its sound ordered effect
   transformation.

We say that $\mathsf{ShallowHandlerPackage}(\Delta,h,\Phi_h)$ holds when:

1. **Safety.** Handler reduction has preservation and effect-aware progress.
2. **Boundary equations.** Return, matching and forwarding satisfy their
   declared operational/semantic equations.
3. **Semantic commutation.** Direct handling agrees with the structural
   shallow map.
4. **Adequacy.** Operational and denotational handled observations agree.
5. **Conservativity and boundary discipline.** Handler-free terms are
   unchanged and one shallow pass stops after its first match.

The bundled name contains the first four layered records and conservativity.
It contains `ShallowElimination` only when explicitly stated; a partial handler
can therefore have a complete safety/semantics/adequacy theorem without
claiming removal of $\Delta$.

The principal conditions are

$$
\begin{aligned}
\mathsf{hpres}:&\quad
\Gamma\vdash M:A!e\Rightarrow
\Gamma\vdash\mathsf{shallow}_\Delta(M,h):C!\Phi_h(e),\\
\mathsf{commute}_h:&\quad
\llbracket\mathsf{shallow}_\Delta(M,h)\rrbracket
=\mathsf{sh}_{\Delta,h}(\llbracket M\rrbracket),\\
\mathsf{adequate}_h:&\quad
\mathsf{obs}_{\mathrm{op}}(\mathsf{shallow}_\Delta(M,h))
=\mathsf{obs}_{\mathrm{den}}(\mathsf{sh}_{\Delta,h}(\llbracket M\rrbracket)),\\
\mathsf{conservative}_h:&\quad
M\in L_B+\Sigma\Rightarrow
\llbracket M\rrbracket_{+h}=\llbracket M\rrbracket_{\mathsf F}.
\end{aligned}
$$

### Theorem III.6 `[C3-MAIN.6.4]` — layered shallow packages [[Lean: source theorem]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageShallowStep.preserve#doc)

Let $J\subseteq I_\Delta$. Then:

1. `OpFreeExtensionPackage + HandlerTyping` yields `ShallowSafety`.
2. `CarrierStructure + MonadExtensionLaws + HandlerTyping` yields
   `ShallowSemantics` by the four-constructor induction.
3. Adding `RelationLaws + HandlerStructuralLaws` yields `ShallowRelationLaws` for the
   structural lifting.
4. Adding `FiniteAdequacyAssumptions + TTClosure + HandlerTTClosure` yields
   `ShallowAdequacyAssumptions`.
5. `EliminationLaws` is not used in conclusions 1--4. If $J=I_\Delta$ and
   `EliminationLaws` holds, the corresponding `ShallowElimination` is obtained.
   In particular, exhaustive `AffineHandlerLaws` yields

   $$
   b\Delta e\longmapsto be'e
   $$

   on its declared anchored domain.

The bundled `ShallowHandlerPackage` follows from conclusions 1--4 and conservativity;
the elimination field is attached only under conclusion 5.

## 7. What is passed to Chapter IV

The residual-context, rule-analysis and finite-tree inductions are expanded in
[Chapter III — detailed shallow-handler proofs](chapter-3-proof-details-v5.md).

Chapter IV receives the standard shallow continuation interface, not just the
response-only sugar.  Nonmatching continuations already retain the shallow
handler; it recursively wraps matching continuations to derive deep handling.
It must add a recursion principle and
prove the resulting recursive effect bound; neither follows from
`ShallowHandlerPackage` alone.
