# Recursive theorems: safety, adequacy, and deep elimination

:::{admonition} Lean correspondence — recursive results
:class: tip
The canonical generic package is [`GenericRecursiveResumption`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumption#doc), with main theorem [`main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumption.main#doc). Morphism, relation, and TT conclusions have separate checked lifts; see the [Chapter-IV table](review-guide.md#chapter-iv-recursion-and-derived-deep-handling).
:::

### Numbered-statement inventory

| statement | review status | correspondence |
|---|---|---|
| Definition IV.1, recursive local package | Lean checked counterpart | [`GenericRecursiveResumption`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumption#doc) |
| recursive preservation/progress | Lean checked directly | [`LanguageStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc), [`HasLanguageComp.progressClosed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed#doc) |
| finite-to-recursive operational inclusion | Lean checked | [`LanguageStep.toRecursive`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.toRecursive#doc) |
| derived/deep coincidence | Lean checked semantically by shallow reinstallation functional | [`RecursiveResumptionSystem.functional`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.RecursiveResumptionSystem.functional#doc) |
| exhaustive-interface elimination | Lean checked source-boundary theorem under exhaustiveness | [`recLanguageHandlerExhaustive_no_escaping_selected_request`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.recLanguageHandlerExhaustive_no_escaping_selected_request#doc) |
| recursive adequacy transport | Lean checked | [`GenericRecursiveResumption.main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumption.main#doc) |
| Definition IV.2 and layered theorem | readable paper decomposition; Lean conclusions linked separately | [`LanguageRecursiveModel.main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveModel.main#doc) |

## Status

**Conditional paper theorem.**  This page records exactly what must be added
to `ShallowHandlerPackage` and what is then preserved.

The source boundary is literal in Lean. Chapters I–III quantify over
`FinLanguageComp`; Chapter IV quantifies over `RecLanguageComp`. The inclusion
commutes with renaming and substitution and simulates every finite reduction
by one recursive reduction. Adding recursion therefore does not retroactively
put a fixed point into the finite language.

## 1. Definition IV.1 `[C4-MAIN.1.1]` — layered recursive packages [[Lean: counterpart]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumption#doc)

For a recursive extension $L^{\mathsf{rec}}$ and recursive carrier $\mathsf R$,
define the following records.

1. $\mathsf{RecursiveSafety}(L^{\mathsf{rec}})$ contains recursive typing,
   unfolding preservation and support-wise one-step progress.
2. $\mathsf{RecursiveModel}(\mathsf R)$ contains pointed $\omega$-cpos,
   continuous semantic constructors, the recursive resumption solution,
   source/semantic fixpoint agreement and Kleene approximation.
3. $\mathsf{RecursiveTTClosure}(\mathsf R,\mathcal O)$ contains a bottom-containing
   admissible pole, continuous TT operations and the fixed-point compatibility
   used by the recursive fundamental lemma.
4. $\mathsf{EffectClosure}(K)$ contains the monotone iteration closure and
   its unit/iteration inequalities.
5. $\mathsf{RecursiveObservation}(\ell)$ selects finite-boundary,
   termination/divergence or productive-infinite observation and supplies
   reflection exactly at that level.

The bundled abbreviation
$\mathsf{RecBasePackage}(L^{\mathsf{rec}},\mathsf R,K,\mathcal O,\ell)$ is the
conjunction of these five records. The following list expands their mathematical
content; it is explanatory and does not merge them back into one indivisible
premise.

1. **Recursive typing.** Unfolding is well typed and preserves the declared
   computation type and effect bound.
2. **Domain structure.** Every carrier is a pointed $\omega$-cpo and the
   semantic constructors are continuous.
3. **Iteration agreement.** Source fixpoints denote least fixed points and
   Kleene approximation computes them.
4. **Admissible TT pole and resumptions.** The recursive observation pole
   contains bottom and is closed under approximation suprema; bind and the
   TT operations are continuous; the recursive carrier satisfies the stated
   resumption equation.
5. **Observation level and effect closure.** The package selects what is
   observed and supplies a monotone iteration closure $K$ for ordered effects.

The principal typing, domain and admissibility fields are represented by

$$
\begin{aligned}
\mathsf{unfoldTy}:&\quad
\Gamma,f:A\xrightarrow{e}B,x:A\vdash M:B!e,\\
\mathsf{unfoldPres}:&\quad
\Gamma\vdash\mathsf{call}(\mathsf{rec}\ f(x).M,V):B!e
\Rightarrow\Gamma\vdash M[f_{\mathsf{rec}}/f,V/x]:B!e,\\
&\forall A.\ (\mathsf R A,\sqsubseteq,\bot)
\text{ is a pointed $\omega$-cpo},\\
\mathsf{iter}(F):&\quad
\operatorname{lfp}(F)=\bigsqcup_{n<\omega}F^n(\bot)
\quad(F\text{ continuous}),\\
\mathsf{fixAgree}:&\quad
\llbracket\mathsf{fix}\ f.M\rrbracket
=\operatorname{lfp}(\lambda f.\llbracket M\rrbracket),\\
\mathsf{admRel}:&\quad
(x_n\mathrel R y_n)_{n<\omega}\Rightarrow
\bigsqcup_nx_n\mathrel R\bigsqcup_ny_n.
\end{aligned}
$$

Here $R$ is the recursive graded TT relation induced by an admissible pole;
the sufficient conditions are proved in the
[recursive TT audit](recursive-tt-audit-v5.md).

The remaining resumption and effect-closure fields include

$$
\mathsf{resIso}_{A}:\quad
\mathsf R A\cong T(A+\Sigma(\mathsf R A)),
$$

$$
K:\widehat E\to\widehat E,qquad
1\leq K(e),qquad e\cdot K(e)\leq K(e),qquad
e\leq f\Rightarrow K(e)\leq K(f).
\tag{Closure}
$$

`cont` states that return, bind, base/free constructors and the Chapter-III
shallow map preserve suprema of $\omega$-chains.  `obsLevel` explicitly selects
finite-boundary, bottom/divergence, or productive-infinite observation and
supplies the corresponding reflection map.

The model, TT, closure and observation records are genuine additional
hypotheses, but they are not needed for one-step recursive safety. They cannot
be reconstructed from the finite `ShallowHandlerPackage` or from monad laws.

For the recursive Writer completion, result typing is factored through
[`LanguageRecursiveBoundaryTyping`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveBoundaryTyping#doc).
It asks exactly for type preservation at a visible base response and at a
matched free request; internal steps use ordinary preservation. This is an
explicit premise, not an implicit reuse of the finite request theorem.

## 2. Recursive safety

:::{prf:theorem} `[C4-MAIN.2.1]` Recursive preservation and progress [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.language_deep_writer_semantic_adequacy#doc)
:label: thm-recursive-preservation-v5

If

$$
\mathsf{ShallowSafety}(\Delta,J,h,\Phi_h)
\land\mathsf{RecursiveSafety}(L^{\mathsf{rec}}),
$$

then

$$
\begin{aligned}
&\Gamma\vdash M:A!e\land M\to M'
 \Rightarrow\Gamma\vdash M':A!e,\\
&\vdash M:A!e\Rightarrow
 \mathsf{Boundary}(M)\mathbin{\dot\vee}\mathsf{UniquePos}(M),\\
&M'\in\operatorname{supp}(\mathsf{step}(M))
 \Rightarrow\vdash M':A!e.
\end{aligned}
$$

Consequently, every maximal supported branch reaches a classified boundary or
is infinite.
:::

The final alternative is new: normalization from the recursion-free chapters
does not survive.

## 3. Derived/deep coincidence

:::{prf:theorem} `[C4-MAIN.3.1]` Derived source handler equals semantic deep handler [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.RecursiveResumptionSystem.functional#doc)
:label: thm-derived-deep-coincidence-v5

If $\mathsf{RecursiveModel}(\mathsf R)$ holds, the Chapter-III shallow map and
the clause functional are continuous, then

$$
\llbracket\mathsf{deep}_{\Delta,h}^{\mathsf{derived}}(M)\rrbracket
=\operatorname{lfp}(\mathcal D_h)(\llbracket M\rrbracket),
\qquad
\operatorname{lfp}(\mathcal D_h)=
\bigsqcup_n\mathcal D_h^n(\bot).
$$
:::

**Proof.**  Unfolding the source `loop` once gives exactly the Chapter-III
shallow map whose matching continuations are wrapped by the previous
approximation; nonmatching continuations remain under that shallow map.  Hence
the $n$th source approximant denotes
$\mathcal D_h^n(\bot)$.  Continuity and the source-fixpoint agreement field
identify their suprema. $\square$

## 4. Deep elimination

:::{prf:theorem} `[C4-MAIN.4.1]` Elimination of an exhaustive interface [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.recLanguageHandlerExhaustive_no_escaping_selected_request#doc)
:label: thm-deep-elimination-v5

If

$$
\mathsf{Exhaustive}_\Delta(h)
\land\mathsf{ClauseFree}_\Delta(h)
\land\mathsf{WrappedMatch}(h)
\land\mathsf{TransparentForward}(h),
$$

then

$$
\forall n,C.\quad
\mathsf{deep}^{\mathsf{derived}}_{\Delta,h}(M)\to^n C
\Rightarrow\neg\mathsf{EscapingReq}_\Delta(C).
\tag{Deep-Elim}
$$
:::

**Proof sketch.**  Induct on finite unfoldings and finite reductions.  A
matching request enters a clause; a nonmatching request is rebuilt with the
invariant in its continuation.  Admissibility closes the semantic statement
at the least fixed point.  Divergence does not invalidate the prefix safety
invariant.

In Lean, `EscapingSelectedRequest` is the directly checkable boundary
predicate: the current head is a selected free request for which lookup
returns `none`. Exhaustiveness rules this out for every configuration, hence
also for every member of any finite execution prefix; termination is not used.

## 5. Adequacy

:::{prf:theorem} `[C4-MAIN.5.1]` Recursive adequacy transport [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumption.main#doc)
:label: thm-recursive-adequacy-v5

If

$$
\mathsf{Admissible}(R)
\land\mathsf{Compat}_{\mathsf{iter}}(R)
\land\mathsf{Compat}_{h}(R)
\land\mathsf{Reflect}_{\ell}(R,\mathsf{obs}),
$$

then, for every closed ground $M$,

$$
M\Downarrow_{\ell}o
\Longleftrightarrow
\mathsf{observe}_{\ell}(\llbracket M\rrbracket)=o.
$$

Here $\ell$ is exactly the observation level stored in
`RecursiveObservation`; no
stronger divergence or productive-infinite conclusion is implicit.
:::

The recursion case uses fixed-point induction.  The handler case uses the
derived/deep coincidence theorem rather than assuming a primitive deep
operator.

## 6. Ordered-effect theorem

For each finite unfolding, Chapter III transforms occurrences in their
original order, taking the prefix before each first match to be $\Delta$-free.
For unbounded recursion, suppose $e^*$ safely closes finite
iteration and $\Phi_h$ is continuous/closure-compatible.  Then the transformed
recursive bound is safely covered by the corresponding closed output, for
example

$$
(b\cdot\Delta\cdot e)^*
\longmapsto
(b\cdot e'\cdot e)^*.
$$

This is an inequality-level may-effect result.  Exact equality, multiplicity,
or a least principal word is outside the basic theorem.

## 7. Chapter-IV structure-preservation theorem

The abstract recursive implication is checked by
[`LanguageRecursiveModel.main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveModel.main#doc).
Its concrete ordered-language Writer adequacy theorem is
[`language_deep_writer_semantic_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.language_deep_writer_semantic_adequacy#doc).

### Definition IV.2 `[C4-MAIN.7.1]` — layered derived-deep packages [[Lean: source package]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveModel#doc)

Define:

1. `RecursiveSafety` by recursive preservation/progress and old-language
   operational conservativity;
2. `DerivedDeepPackage` by source definability, the least-fixed-point equation
   and the return/match/forward deep equations;
3. `RecursiveHandlerRelation` by admissible relation preservation through the
   derived handler functional;
4. `RecursiveAdequacyAssumptions` by adequacy at the selected observation level;
5. `DeepElimination` by absence of escaping handled-interface requests on every
   finite prefix;
6. `RecursiveEffectLaws` by closure of transformed finite effects under $K$.

The bundled name $\mathsf{DeepHandlerPackage}(\Delta,h,\Phi_h,K)$ contains the first
four records and `RecursiveEffectLaws`. `DeepElimination` is attached only when
the handler has `EliminationLaws` and its clauses do not re-emit $\Delta$.
Thus a partial derived handler still has a deep semantics and adequacy theorem
without a false interface-elimination claim.

Their contents are read separately as follows:

1. **Recursive safety and conservativity.** Preservation/progress hold at each
   step and old programs retain their behavior.
2. **Derived-deep definability.** The source construction denotes the least
   fixed point of the semantic handler functional.
3. **Deep equations.** Return, matching and forwarding satisfy the standard
   deep-handler equations.
4. **Declared adequacy.** Adequacy holds at the selected observation level.
5. **Iteration bound.** Transformed recursive effects remain below the
   closure bound.
6. **Optional interface elimination.** When `DeepElimination` is separately
   established, no finite outward observation exposes an unhandled $\Delta$
   request.

The characteristic conditions are

$$
\begin{aligned}
\mathsf{defDeep}:&\quad
\mathsf{deep}^{\mathsf{derived}}_{\Delta,h}
=\operatorname{lfp}(\mathcal D_h),\\
\mathsf{eliminate}_\Delta:&\quad
\forall n,C.\quad\mathsf{deep}^{\mathsf{derived}}_{\Delta,h}(M)\to^nC
\Rightarrow\neg\mathsf{EscapingReq}_\Delta(C),\\
\mathsf{iterEffect}:&\quad
\Phi_h((b\cdot\Delta\cdot e)^*)
\leq(b\cdot e'\cdot e)^*,
\quad e^*:=K(e).
\end{aligned}
$$

:::{prf:theorem} `[C4-MAIN.7.2]` Layered recursive derived-deep packages [[Lean: source theorem]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.language_deep_writer_semantic_adequacy#doc)
:label: thm-recursive-derived-deep-package-v5

The conclusions and their premises are separate implications:

1. `ShallowSafety + RecursiveSafety` implies `RecursiveSafety`.
2. `ShallowSemantics + RecursiveModel`, together with continuity of the
   handler functional, implies `DerivedDeepPackage`.
3. `ShallowRelationLaws + RecursiveModel + RecursiveTTClosure`, together with continuity of
   the related handler functionals, implies `RecursiveHandlerRelation` by
   fixed-point induction.
4. `ShallowAdequacyAssumptions + RecursiveModel + RecursiveTTClosure +`
   $\mathsf{RecursiveObservation}(\ell)$ implies `RecursiveAdequacyAssumptions`
   exactly at level $\ell$.
5. `HandlerTyping + EffectClosure` and closure compatibility of
   $\Phi_h$ imply `RecursiveEffectLaws`.
6. `ShallowSafety + RecursiveSafety + EliminationLaws`, outward
   $\Delta$-free clauses and wrapped matching resumptions imply
   `DeepElimination`.

Conclusions 1--5 give the non-eliminating `DeepHandlerPackage`. Conclusion 6 may be
attached when its stronger premises hold.
:::

## 8. Sharp limits

The fixed-point induction, elimination invariant and recursive logical-relation
argument are expanded in
[Chapter IV — detailed recursive and derived-deep proofs](chapter-4-proof-details-v5.md).

The theorem does not provide termination, exact effect counts, unrestricted
multi-shot resource safety, commutation with old handlers, full abstraction,
or productive traces in a bottom-only model.  These require separate
packages rather than stronger prose around “an arbitrary base effect.”
