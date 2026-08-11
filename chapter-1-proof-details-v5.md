# Appendix I-A — detailed Chapter I proofs

:::{admonition} Review role
:class: note
This is a proof appendix, not an additional step in the main reading path.
Use the [Chapter-I mapping](review-guide.md#chapter-i-fixed-base-language) to
distinguish kernel-checked lemmas from recursion-free normalization arguments
that remain paper proofs.
:::

## 1. Preliminary lemmas

We work modulo alpha-renaming and use capture-avoiding substitution.

:::{prf:lemma} `[C1-PROOF.1.1]` Weakening [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.rename_preserved#doc)
:label: lem-i-weakening-v5

If $\Gamma\vdash J$ and $x\notin\mathrm{dom}(\Gamma)$, then
$\Gamma,x:A\vdash J$.
:::

**Proof.** Induction on the derivation of $J$.  Every premise is weakened by
the induction hypothesis.  Variable lookup uses the original membership;
effect annotations are unchanged. $\square$

:::{prf:lemma} `[C1-PROOF.1.2]` Value and computation substitution [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.subst_preserved#doc)
:label: lem-i-substitution-v5

If $\Gamma,x:A\vdash J$ and $\Gamma\vdash W:A$, substituting $W$ for $x$
preserves $J$ and its effect annotation.
:::

**Proof.** Simultaneous induction on the last typing rule.  Variables split
into $x$ and $y\ne x$.  Lambda binders are alpha-renamed and use weakening.
Pairs, injections and case follow componentwise.  General application follows
by applying the computation induction hypotheses first to the function and
then to the argument; its annotation remains $e_M\cdot e_N\cdot e$.  In
`let y <- M in N`, apply the computation induction hypothesis to $M$ and,
after alpha-renaming $y$, to $N$; the resulting grade remains $b\cdot c$.
For a primitive $\beta(V)$ apply the value hypothesis to $V$ and reapply its
fixed typing rule.  Subeffecting reuses the same inequality.  These exhaust
the grammar. $\square$

## 2. Preservation

:::{prf:lemma} `[C1-PROOF.2.1]` Application elaboration [Derived notation]
:label: lem-i-application-elaboration-v5

If

$$
\Gamma\vdash M:(A\xrightarrow{e}B)!e_M
\quad\text{and}\quad
\Gamma\vdash N:A!e_N,
$$

then the fine-grain elaboration of $M\,N$ has type
$B!(e_M\cdot e_N\cdot e)$ and evaluates $M$, $N$, and the function body in
that order.
:::

**Proof.** Under $f:A\xrightarrow{e}B$, core application of $f$ to the value
$x:A$ has effect $e$.  The inner `let` therefore has effect $e_N\cdot e$.
The outer `let` has effect $e_M\cdot(e_N\cdot e)$, equal to the claimed grade
by associativity.  The two nested `let` evaluation contexts enforce the same
left-to-right order. $\square$

:::{prf:theorem} `[C1-PROOF.2.2]` Internal preservation [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc)
:label: thm-i-preservation-detail-v5

If $\Gamma\vdash M:A!b$ and $M\to M'$, then
$\Gamma\vdash M':A!b$.
:::

**Proof.** By induction on the reduction derivation.  For beta reduction and
`let x <- return V in N`, use substitution.  Product and sum eliminations use
the corresponding value inversion followed by substitution.  For a reduction
under an evaluation context, induction on the context proves the replacement
lemma

$$
\Gamma\vdash M:A!b,\ M\to M'
\implies
\Gamma\vdash\mathcal E[M]:C!d
\Rightarrow\Gamma\vdash\mathcal E[M']:C!d.
$$

The `let` context is the only primitive effectful core case: both sides receive the same
$b\cdot c$, and reassociation uses monoid associativity.  Subeffecting closes
the derivation at the originally declared $d$.  General application follows
through the elaboration lemma. $\square$

## 3. Unique decomposition

:::{prf:lemma} `[C1-PROOF.3.1]` Canonical values [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageVal.closed_arr_canonical#doc)
:label: lem-i-canonical-v5

A closed value of function, product, sum, unit, or base type has the
corresponding introduction form.
:::

**Proof.** Inversion of the value typing derivation; a closed variable case is
impossible. $\square$

:::{prf:theorem} `[C1-PROOF.3.2]` Unique base decomposition [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageProgress.kind_unique#doc)
:label: thm-i-decomposition-detail-v5

Every closed typed computation is exactly one of a return, a uniquely located
internal redex, or a uniquely exposed base request.
:::

**Proof.** Structural induction on the computation.  Introduction forms are
immediate.  For elimination and sequencing, first decompose the selected CBV
subcomputation.  If it steps, extend its unique context; if it returns, the
canonical-values lemma determines either the unique principal redex or the
next selected subcomputation; if it exposes a request, extend its context.
The evaluation-context grammar has one selected hole, so two decompositions
would induce two decompositions of the same strict subterm.  The induction
hypothesis makes them equal.  The three outer forms are syntactically
disjoint. $\square$

## 4. Recursion-free normalization

Restrict terms to the Lean type
[`FinLanguageComp`](https://myuon.github.io/effect-semantics-notes/lean/EffectSemantics/Syntax/LanguageCalculus.html).
The fragment is substitution-closed and step-closed by construction.
Define reducible values $\mathcal V_A$ and computations $\mathcal C_A$ by
type recursion.  A computation is in $\mathcal C_A$ when every branch in the
support of the base response kernel reaches a classified observation, and a function value
is in $\mathcal V_{A\xrightarrow{b}B}$ when it maps every $\mathcal V_A$ argument to
$\mathcal C_B$.

:::{prf:conjecture} `[C1-PROOF.4.1]` Fundamental reducibility lemma [Formalization boundary]
:label: lem-i-reducibility-v5

If $\Gamma\vdash J$, every closing substitution mapping variables to
reducible values maps $J$ to the corresponding reducibility predicate.
:::

**Proof.** Induction on typing.  The function case extends the closing
substitution with a reducible argument.  `let` first normalizes its left
computation; on return, substitution and the induction hypothesis apply to
the body; a terminal base outcome remains terminal.  A primitive is reducible
by the base-package termination hypothesis.  Products, sums and cases are
standard.  Subeffecting does not change the term. $\square$

:::{prf:conjecture} `[C1-PROOF.4.2]` Recursion-free normalization [Formalization boundary]
:label: thm-i-normalization-detail-v5

Every closed typed Chapter-I computation $M:A!b$ in
`FinLanguageComp` has a well-defined operational interpretation
$\mathsf{run}_S(M)\in S_b\llbracket A\rrbracket$.
:::

**Proof.** Apply the fundamental lemma to the empty substitution.  Each branch
is covered by computation reducibility.  Unique decomposition fixes the next
evaluation position; the typed response map supplies the possibly many
successors at a primitive request.  Branchwise well-foundedness therefore
defines the $S$-structured result. $\square$

The fragment boundary and its structural closure are kernel-checked. This
outline is not yet a kernel-checked normalization proof: it still requires the
logical-reducibility development and a well-founded response-kernel premise.

## 5. Semantic soundness and effect safety

In the mechanized response-tree semantics, semantic sequencing/substitution is
[`ProducesLanguageWriterTree.letE`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.letE#doc), and one-step invariance is
[`ProducesLanguageWriterTree.internalStepInvariant`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.internalStepInvariant#doc).
For a total categorical model, semantic substitution is proved simultaneously for values and computations by
typing induction.  The binder cases use functoriality, strength naturality and
the monad laws; primitives use naturality of their supplied interpretation.
Each principal reduction equation then follows respectively from semantic
substitution, a unit law, or a coproduct beta law.  Congruence follows because
graded bind and the categorical constructors respect equality.

For effect safety, prove by induction on evaluation contexts the residual
factorization lemma: if a request of grade $c$ is exposed in
$\mathcal E[\beta(V)]$ typed at $b$, there are prefix and suffix grades $p,q$
with $p\cdot c\cdot q\le b$.  Preservation keeps the same outer bound along
internal steps.  Hence every executed request is covered at its ordered
position.  A discarded conditional branch merely removes a possible factor
and never proves the converse.

## 6. Adequacy for the three instances

For Writer use the invariant

$$
w_{\mathrm{acc}}\cdot
\pi_1\llbracket M\rrbracket=w_{\mathrm{final}}.
$$

One machine step preserves it by associativity; termination and semantic
soundness give both directions.  State uses the analogous invariant
$\llbracket M\rrbracket(s_{\mathrm{current}})=(v,s_{\mathrm{final}})$.
Exception uses induction on the finite run and the two defining bind equations
for return and error.  Constructor disjointness supplies reflection in all
three deterministic cases, viewed as Dirac $\mathcal K$-observations.

For `randomBool`, induction on the finite response tree uses the Kleisli laws
of $\mathsf{SubDist}$: each operational response weight is multiplied along a
branch and summed at joins, exactly as in denotational bind.  Hence

$$
\Pr[M\Downarrow o]
=\mathsf{observe}(\llbracket M\rrbracket)(o).
$$

These four proofs establish the corresponding fields of the split
`BaseSafetyCert`, `BaseModelCert` and `BaseAdequacyCert`; determinism is
an instance property, not a certificate premise.
