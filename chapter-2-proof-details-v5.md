# Chapter II — detailed free-extension proofs

:::{admonition} Review role
:class: note
This appendix explains proofs whose canonical Lean declarations are listed in the [Chapter-II correspondence table](review-guide.md#chapter-ii-free-operations). A theorem without an individual API link here should be read as a paper derivation, not silently as mechanized.
:::

## 1. Operational lemmas

Substitution is the Chapter-I simultaneous induction with one additional
case.  For $\mathsf{op}_{\Delta,i}(V)$, substitute in $V$ and reapply
`T-Free`; there is no source continuation premise.  Preservation has no new
principal reduction because a free operation is an exposed boundary.

For four-way decomposition, repeat the Chapter-I structural induction.  The
new operation form gives the free-request alternative.  In a `let` context,
an exposed request is uniquely paired with the residual continuation
$\lambda r.\mathcal E[\mathsf{return}\,r]$.  Disjoint outer constructors and
Chapter-I uniqueness prove exclusivity.

If a term whose bound contains no free factor exposed a free request, the
residual factorization lemma would produce
$p\cdot\Delta\cdot q\le e$.  The stipulated no-erasure property of the
extended preorder contradicts absence of $\Delta$ from $e$.  This proves
empty-free-effect safety.

## 2. Construction of bind

Fix $f:A\to\mathsf F_f B$.  On the initial algebra defining
$\mathsf F_e A$, give the target carrier $\mathsf F_{e\cdot f}B$ the algebra
whose actions are:

- a return $a$ is sent to $f(a)$;
- a base layer is mapped using base bind/strength;
- $\mathsf{op}(p,k)$ is rebuilt as
  $\mathsf{op}(p,\lambda r.k(r)\mathbin{\gg=}f)$.

Initiality yields one map, written $(-)\mathbin{\gg=}f$.

:::{prf:theorem} `[C2-PROOF.2.1]` Free graded-monad laws [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericFreeExtensionStructurePreservation#doc)
:label: thm-ii-free-monad-laws-v5

The resulting return and bind satisfy both unit laws and associativity, and
commute with coherent weakening.
:::

**Proof.** For each equation, both sides are algebra morphisms from the same
initial algebra.  On returns the equation is respectively substitution,
identity, or ordinary function composition.  On a base layer it is the
corresponding law of $T$.  On a free generator both sides rebuild the same tag
and parameter, and their continuations agree by the uniqueness/induction
hypothesis.  Initiality therefore identifies the maps.  For weakening, compare
the two algebra morphisms obtained by weakening before or after recursion;
base coherence and identical generator actions make them equal. $\square$

Strength is constructed by the same fold, sending
$(x,\mathsf{op}(p,k))$ to
$\mathsf{op}(p,\lambda r.(x,k(r)))$.  Naturality and strength laws again follow
by initiality after checking returns, base layers and generators.

## 3. Base embedding and conservativity

Define $j:T_eA\to\mathsf F_eA$ by mapping a base computation into the base
layer and returning its values through the free return constructor.  The unit,
bind, strength and weakening squares commute by their defining folds.

Induction on an old typing derivation proves
$\llbracket M\rrbracket_{\mathsf F}=j\llbracket M\rrbracket_T$.  The `let`
case uses the bind square, primitives use their lifted definition, and
subeffecting uses the weakening square.  Operational conservativity is a
separate syntax induction: no new rule has an old left-hand side.

## 4. Adequacy lifting

Choose the operational/denotational observation pole supplied by
`BaseAdequacyCert`; semantic bind and primitive compatibility come from
`BaseModelCert`.
Its graded TT-lifting gives a base computation relation
$V_A^{\top\top}$.  Structurally lift it to
$\mathsf{Str}_\Delta(V_A^{\top\top})$ between closed computations and free
denotations:

- returns relate when their values do;
- classified base outcomes relate by `BaseAdequacyCert`;
- free requests relate only when tags and parameters relate and, for every
  related response, their continuations are again in $R$.

Pole closure gives
$\mathsf{Str}_\Delta(V_A^{\top\top})\subseteq
V_A^{\top_\Delta\top_\Delta}$.  Because the calculus is recursion-free, assign each computation the finite
height of its operational/free tree.  Prove the fundamental statement by
induction on this height, with a subsidiary typing induction for source
constructors.  A maximal initial base segment is discharged by base adequacy.
At a free boundary, constructor separation identifies the unique tag and the
height strictly decreases after any response.  This proves both preservation
and reflection of returns, old outcomes, and free requests; `observeReflect`
turns the final TT relation into adequacy.

## 5. Morphisms and relations

For a compatible $q:T\Rightarrow U$, equip the target free carrier with the
source algebra transported by $q$.  Initiality yields $\mathsf F(q)$.
Identity and composition follow because the competing lifts agree on all
three constructors. For a compatible graded relator
$\overline{T,U}_b(R)$, define the least structural free relation
$\mathsf{Str}_\Delta(R)$ by applying the relator to the recursively generated
base-layer payload relation. Prove bind closure by induction on the left tree;
the base case is exactly `Rel-Act`. The separate TT transport
then proves
$\mathsf{Str}_\Delta(V^{\top\top})\subseteq
V^{\top_\Delta\top_\Delta}$ from pole closure.  Thus the relation components of
`FreeCert` follow without identifying structural generation with
observational closure.

:::{prf:theorem} `[C2-PROOF.5.1]` Graph lemma [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FreeExtension.Rel.graphMapSignature#doc)
:label: thm-ii-graph-lemma-detail-v5

For every compatible $q:T\Rightarrow U$,

$$
\mathsf{Str}_\Delta(\overline q)
=\operatorname{Graph}(\mathsf F_\Delta q).
$$
:::

**Proof.**  For the forward inclusion, induct on the lifted-relation
derivation.  Each constructor forces the right component to be the
corresponding clause of the fold defining $\mathsf F_\Delta q$.  For the
reverse inclusion, induct on the source free carrier.  Return and free-node
cases are immediate; a base layer uses membership in
$\operatorname{Graph}q$ and the pointwise induction hypothesis. $\square$

This identifies relation lifting with morphism lifting on graphs; it is
stronger than merely constructing the two liftings independently.
