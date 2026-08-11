# Chapter I — metatheory and base certificate

:::{admonition} Lean correspondence — theorem bundle
:class: tip
**Lean checked components:** substitution and typing live in [`LanguageRenameSubst`](https://myuon.github.io/effect-semantics-notes/lean/EffectSemantics/Syntax/LanguageRenameSubst.html), preservation in [`LanguageStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc), progress in [`HasLanguageComp.progressClosed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed#doc), and the exact mechanized bundle in [`LanguageFiniteStructureCert`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageFiniteStructureCert#doc). The broader categorical `BaseCert` notation remains a readable abstraction. [Statement-by-statement map](review-guide.md#chapter-i-fixed-base-language).
:::

### Numbered-statement inventory

| statement | review status | correspondence |
|---|---|---|
| Lemma I.1–I.2, substitution | Lean checked | [`HasLanguageComp.subst_preserved`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.subst_preserved#doc) |
| Theorem I.3, preservation | Lean checked | [`LanguageStep.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc) |
| Theorem I.4, effect-aware progress | Lean checked | [`HasLanguageComp.progressClosed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed#doc), [`LanguageProgress.kind_unique`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageProgress.kind_unique#doc) |
| Theorem I.5, deterministic internal reduction | Lean checked | [`LanguageStep.deterministic`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.deterministic#doc) |
| Conjecture I.6, recursion-free normalization | Precisely scoped formalization boundary | `FinLanguageComp` excludes recursion by construction and is substitution/reduction closed; reducibility normalization remains future work |
| Lemma I.7–Theorem I.8, semantic substitution/soundness | Lean checked for the relational Writer/free-tree semantics | [`letE`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.letE#doc), [`internalStepInvariant`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.internalStepInvariant#doc) |
| Theorem I.9, effect upper-bound safety | Lean checked component | [`HasLanguageEffect.observationMember`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.TypedWriterTree.HasLanguageEffect.observationMember#doc) |
| Definition I.1 and Boundary I.10, `BaseCert` | Paper certificate packaging | component theorems above |

## Status

**Paper proof package.**  This page extracts exactly what Chapter II may assume
when it adds free operations.

## 1. Syntactic substitution

### Lemma I.1 `[C1-CERT.1.1]` — value substitution [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageVal.subst_preserved#doc)

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

### Lemma I.2 `[C1-CERT.1.2]` — computation substitution [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.subst_preserved#doc)

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

### Theorem I.3 `[C1-CERT.2.1]` — internal preservation [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.preserve#doc)

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

### Theorem I.4 `[C1-CERT.2.2]` — effect-aware progress [[Lean: exact statement]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed_exactlyOne#doc)

If

$$
\vdash M:A!b,
$$

then exactly one of the following three alternatives holds:

$$
\begin{aligned}
&\exists V.\ M=\mathsf{return}\,V,\\
&\exists M'.\ M\longrightarrow M',\\
&\exists \mathcal E,\beta,V.\ M=\mathcal E[\beta(V)].
\end{aligned}
\tag{I.4}
$$

Here $\mathcal E$ ranges over call-by-value evaluation contexts and $\beta$ is
a base-language primitive.  Thus a closed well-typed computation has returned,
can make an internal step, or has exposed one request to the base machine.
These alternatives are mutually exclusive.  An exposed request is an
operational boundary rather than a stuck term: the base machine may answer it
and resume the computation.

The linked Lean theorem states this three-way alternative and its pairwise
exclusivity directly.  Its exhaustiveness is derived from
[`progressClosed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed#doc),
and exclusivity from
[`kind_unique`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageProgress.kind_unique#doc).
The reusable Lean development also admits free-operation boundaries; in the
Chapter I fragment, where no free operations occur, its `LanguageBoundary`
case is precisely an evaluation context exposing a base primitive
$\mathcal E[\beta(V)]$.

### Theorem I.5 `[C1-CERT.2.3]` — deterministic internal reduction [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageStep.deterministic#doc)

For all computations $M,M_1,M_2$,

$$
M\longrightarrow M_1\ \land\ M\longrightarrow M_2
\quad\Longrightarrow\quad
M_1=M_2.
\tag{I.5}
$$

This concerns only the language's internal reduction relation.  It neither
asserts that a base request has a unique response nor requires the response
mechanism itself to be deterministic.

## 3. Termination

### Conjecture I.6 `[C1-CERT.3.1]` — recursion-free machine normalization [Formalization boundary]

Assume $M:\mathsf{FinLanguageComp}$ and that the operational interpretations
of the base primitives preserve typing and terminate on this fragment. Then
every closed well-typed Chapter-I program $M:A!b$ induces a well-defined
operational denotation

$$
\mathsf{run}_{S}(M)\in S_b\llbracket A\rrbracket.
$$

This is a totality claim for the finite operational interpretation, not a
claim that an effectful result contains a unique outcome.

### Proof sketch

Use the standard reducibility argument for fine-grain CBV STLC, with the
primitive case discharged by the total operational algebra $\beta^S$.
Function, product and sum cases are standard. Theorem I.4 identifies the
exposed request; graded Kleisli composition in $S$ resumes its continuation.

The recursion-free fragment is the separate Lean type
[`FinLanguageComp`](https://myuon.github.io/effect-semantics-notes/lean/EffectSemantics/Syntax/LanguageCalculus.html).
It is closed by construction under renaming, substitution and internal
reduction; `fixBeta` cannot be constructed. What remains unmechanized is the
reducibility/strong-normalization argument and the explicit well-founded
response-kernel package. The claim is deliberately absent from Chapter IV.

## 4. Denotational soundness

### Lemma I.7 `[C1-CERT.4.1]` — semantic sequencing/substitution [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.letE#doc)

For a computation $M$,

$$
\llbracket M[W/x]\rrbracket
=
\llbracket M\rrbracket
\circ
\langle\mathsf{id},\llbracket W\rrbracket\rangle.
$$

The exact mechanized counterpart is relational: producing `tree` from the
bound and producing `continuation value` from every substituted body entails
that the whole `let` produces `tree.bind continuation`. This is
`ProducesLanguageWriterTree.letE`. The displayed categorical equality is its
paper presentation for a total model satisfying the same bind law.

### Theorem I.8 `[C1-CERT.4.2]` — internal reduction soundness [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.internalStepInvariant#doc)

If $M\to M'$, then

$$
\llbracket M\rrbracket=\llbracket M'\rrbracket.
$$

The exact mechanized statement says: if $M\to M'$ and $M'$ produces a tree,
then $M$ produces the same tree. The displayed equality follows when the
chosen denotation is total and functional; no termination is silently assumed.

## 5. Effect upper-bound safety

### Theorem I.9 `[C1-CERT.5.1]` — effect upper-bound safety [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.effectSound#doc)

If

$$
\vdash M:A!b
$$

then every base primitive that the machine can execute is permitted by the
ordered upper bound $b$ at its typed position.  Effects in $b$ need not execute.

### Proof idea

Effect-aware progress and residual-context typing show that an exposed
$\beta(V)$ occurs with primitive grade $|\beta|$ in the ordered position
assigned by the surrounding `let` contexts.  Internal reduction preserves the
declared bound.  Branch selection may remove potential effects but cannot add
an effect outside the common upper bound.  The selected base package separately
checks that its external response rule implements only the declared primitive.

This is a may-effect theorem.  It is intentionally one-way and introduces no
runtime trace object.

## 6. Operational--denotational comparison

Let $S_b$ be the operational graded monad and $T_b$ the denotational graded
monad. A comparison certificate supplies a graded monad morphism

$$q_{b,A}:T_bA\to S_bA$$

that commutes with weakening, return, bind, strength, and every primitive:

$$q(\beta^T(v))=\beta^S(v).$$

The base adequacy statement is

$$
\mathsf{run}_{S}(M)=q(\llbracket M\rrbracket_T)
$$

for every closed $M:A!b$. When equality is too strong, the package instead
supplies a graded logical relation preserved by the same structure. A ground
observation or TT pole may subsequently quotient or test both sides, but it is
not the carrier of operational effects.

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

For the fixed mechanized base calculus, the operational components are checked
by [`Step.preserve`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.Step.preserve#doc)
and [`HasComp.progressClosed`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasComp.progressClosed#doc).
The Writer instance's operational/tree adequacy is
[`writer_operational_tree_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.writer_operational_tree_adequacy#doc).
These declarations instantiate the concrete formal calculus; they do not by
themselves mechanize the paper-level quantification over every base listed
below.

### Definition I.1 `[C1-CERT.7.1]` — split base certificates [Readable abstraction; mechanized core](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageFiniteStructureCert#doc)

For a base calculus $L_B$ and ordered effect algebra
$E_B=(B,1,\cdot,\leq)$, use four independent records:

1. $\mathsf{BaseSafetyCert}(L_B,E_B)$ contains substitution, preservation,
   exclusive return/redex/request decomposition, deterministic internal
   reduction, finite-fragment normalization, and effect-bound safety.
2. $\mathsf{OperationalModelCert}(L_B,E_B,S)$ contains the operational strong
   graded monad $S_b$, weakening, primitive interpretations $\beta^S$, and
   agreement of its evaluator with the direct machine.
3. $\mathsf{DenotationalModelCert}(L_B,E_B,T)$ contains the denotational
   strong graded monad $T_b$, primitive interpretations $\beta^T$, semantic
   substitution, and reduction soundness.
4. $\mathsf{ModelComparisonCert}(S,T,q)$ contains a graded monad morphism
   $q:T\Rightarrow S$ commuting with strength, weakening, and primitives (or
   the corresponding graded logical relation).

Retain the readable bundled name as

$$
\begin{aligned}
&\mathsf{BaseCert}(L_B,E_B,S,T,q)\\
&\quad:\Longleftrightarrow
\mathsf{BaseSafetyCert}(L_B,E_B)
\land\mathsf{OperationalModelCert}(L_B,E_B,S)\\
&\qquad\land\mathsf{DenotationalModelCert}(L_B,E_B,T)
\land\mathsf{ModelComparisonCert}(S,T,q).
\end{aligned}
\tag{Base-Split}
$$

End-to-end examples may use `BaseCert`; transport theorems cite only the
component certificates they actually use. Observation/pole data is a
subsequent optional layer and is not one of the effect carriers.

If a later TT argument uses finite observations, its pole may separately
require finite branching and constructor separation. Those hypotheses belong
to the observation theorem, not to the operational-model certificate.

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

### Boundary I.10 `[C1-CERT.7.2]` — Base certificate extraction [Instance boundary]

For each $X\in\{\mathsf{Writer},\mathsf{State},\mathsf{Exception}\}$, let
$L_X,E_X,S^X,T^X,q^X$ be the syntax/machine, ordered algebra, operational
model, denotational model, and comparison defined in this chapter. The desired
instance statement is

$$
\forall X\in\{W,S,E\}.\quad
\mathsf{BaseCert}(L_X,E_X,S^X,T^X,q^X).
$$

### Proof

The fields `subst`, `pres`, `uniquePos`, `branchNorm`, and `effsafe` follow
from Theorems I.1–I.6 and I.9 after checking each primitive machine rule. The
Writer, State and Exception constructions must separately supply the graded
structures of $S^X$ and $T^X$. Theorems I.7–I.8 supply `semsubst` and
`redsnd`; primitive commutation plus induction on computations supplies the
comparison theorem. No free-operation or handler property is used.

The generic finite structure certificates below are mechanized. Fully
assembling the revised `writerBaseCert`, `stateBaseCert`, and
`exceptionBaseCert` records is an explicit Lean boundary; this paragraph is
not treated as a proof of those declarations. $\square$

The generic finite structures are kernel-checked by
[`genericWriterExtensionCert`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericWriterExtensionCert#doc),
[`genericStateExtensionCert`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericStateExtensionCert#doc), and
[`genericExceptionExtensionCert`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericExceptionExtensionCert#doc).
Random/SubDist remains a separate unformalized instance and is not part of the
checked extraction claim.

## 8. Boundary exported to Chapter II

Complete derivations for the lemmas used above are given in
[Chapter I — detailed proofs](chapter-1-proof-details-v5.md).

`BaseCert` does not assert that every base has exact grades, that every
denotation exposes a syntactic head event, or that base effects commute with
future free operations.  Chapter II must add visible free-operation nodes
without inspecting an opaque base computation and must prove conservativity
through the supplied embedding.
