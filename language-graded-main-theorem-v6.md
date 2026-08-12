# Main language theorem: structure preservation across all stages

:::{admonition} Canonical checked theorem
:class: tip
This is the source-language summary after the concrete chapters. The finite
and recursive conclusions are linked below as individual Lean theorems rather
than collected into result records. For the base-independent construction,
continue to the [generic finite](generic-free-extension-theorem-v1.md) and
[generic recursive](generic-recursive-resumption-theorem-v1.md) theorems.
:::

This page records the theorem that is now checked in Lean.  It supersedes the
earlier provisional statements that mixed finite ordered words, unordered
rows, and exact runtime traces.

The previously missing base-independent finite construction is now stated in
[Generic finite free-extension theorem](generic-free-extension-theorem-v1.md).

The generated Lean API reference contains the exact checked declarations:

- [`LanguageRecursiveModel.main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveModel.main#doc)
- [`language_deep_writer_semantic_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.language_deep_writer_semantic_adequacy#doc)
- [`LanguageRecursiveMorphism.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveMorphism.lift#doc)
- [`LanguageRecursiveRelation.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveRelation.lift#doc)

## 1. Fixed source language

The source is fine-grain call-by-value with value types

$$
A,B ::= 1\mid\mathsf{Bool}\mid A\times B\mid A+B
       \mid A\xrightarrow{L}B,
$$

where $L$ is a downward-closed language of finite ordered effect words.
Computations include base operations, user-defined free operations,
subeffecting, and effectful recursive functions.  Sequencing uses language
concatenation, while conditional and case effects use language union.

The annotation is a may-effect upper bound.  It need not equal the unique
runtime path, but it retains ordering information between all possible paths.

## 2. Finite theorem `[LG.2.1]` [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.ProducesLanguageWriterTree.answerWith#doc)

For every fixed typed base/free signature, adding free requests and affine
shallow handlers preserves the following structures.

1. Internal CBV reduction preserves result types and effect-language bounds.
2. Every closed typed computation returns, reduces, or exposes one typed
   base/free boundary.
3. Response-typed free trees have a graded monadic bind.
4. Source `let` is interpreted by tree bind.
5. The generated tree is bounded by the declared effect language.
6. Finite Writer runs and tree observations are adequate.
7. Shallow handling is natural under map and preserves structural relations
   and their TT closure.
8. A matching source reduct denotes clause execution followed by the bare
   captured continuation.  The handler is not reinstalled after the match.

Lean packages these conclusions as the individual finite-language theorems.

## 3. Recursive completion and derived deep handling `[LG.3.1]` [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.language_deep_writer_semantic_adequacy#doc)

Let

$$
F_h:(C\to O_\bot)\longrightarrow(C\to O_\bot)
$$

be the one-layer functional obtained by running the source to its next head.
It returns immediately, takes one internal step, interprets one base action,
or applies one shallow matching clause.  Recursive reinstallation of that
same shallow handler is the Kleene least fixed point

$$
\llbracket\mathsf{deep}_h\rrbracket
  =\mu F_h=\bigsqcup_{n<\omega}F_h^n(\bot).
$$

For the Writer instance Lean proves:

$$
F_h(\mu F_h)=\mu F_h,
$$

$$
F_h(X)\sqsubseteq X\Longrightarrow\mu F_h\sqsubseteq X,
$$

and

$$
M\Downarrow_h(w,v)
\quad\Longleftrightarrow\quad
(\mu F_h)(M)=\mathsf{some}(w,v).
$$

If $M:A\,!\,L$, every denoted finite result $v$ still has type $A$.
Thus the shallow-handler typing theorem, recursive operational semantics,
least-fixed-point denotation, adequacy, and ground fundamental property form
one checked proof chain.  These conclusions are packaged as
the individual recursive theorems.

## 4. Abstract base theorem `[LG.4.1]` [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveModel.main#doc)

The recursive proof does not intrinsically require Writer.  An arbitrary base
instance supplies only:

1. an $\omega$-continuous one-layer functional $F$;
2. a direct operational run relation adequate for the finite iterates
   $F^n(\bot)$;
3. a base-specific observation pole $P$ preserved by one application of $F$.

The generic theorem derives, rather than assumes:

- the least-fixed-point unfold law;
- least pre-fixed-point induction;
- adequacy of the completed semantics $\mu F$;
- admissibility and the recursive fundamental pole $P(\mu F)$.

This non-circular premise record is `LanguageRecursiveModel`; its theorem is
`LanguageRecursiveModel.main`.  The Writer model is separately shown to
instantiate it using typed request decomposition and the Unit response law for
Writer operation zero.

## 5. Morphisms and logical relations `[LG.5.1]` [[Lean: morphism]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveMorphism.lift#doc) [[Lean: relation]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageRecursiveRelation.lift#doc)

Let $q:O_S\to O_T$ be a base outcome map.  If it commutes with one semantic
layer, $q_\ast\circ F_S=F_T\circ q_\ast$, then it commutes with recursive
completion:

$$
q_\ast(\mu F_S)=\mu F_T.
$$

Likewise, an admissible binary relation containing bottom and preserved by one
application of $(F_S,F_T)$ relates the two least fixed points.  Pointwise
outcome simulations are proved admissible, so this applies to graph and
logical-relation liftings.

The local premises are recorded by `LanguageRecursiveMorphism` and
`LanguageRecursiveRelation`; their `lift` theorems derive the completed
correspondences.  Morphism lifting and relation lifting are separate results,
while a morphism graph can instantiate the relation theorem.

## 6. Concrete checks

The unit free-operation signature and pure unit clause instantiate the full
recursive package.  Lean checks both:

- a selected request handled to `Unit`; and
- a recursive conditional program that takes an actual `fixBeta` step and
  returns through its false branch.

In both cases operational runs, least-fixed-point denotation, and result typing
agree.

## 7. Exact boundary of the result

The theorem establishes a concrete `Type`-level extension theorem and an
abstract finite-observation completion interface.  It does not claim, without
additional structure:

- productive infinite Writer traces;
- probabilistic or nondeterministic adequacy;
- full abstraction (relation preservation alone is not completeness);
- resource validity of unrestricted multi-shot resumptions;
- a universe-polymorphic theorem over arbitrary categories.

State, Exception, Random, and other bases must discharge the three local
recursive base obligations above.  Their laws are not consequences of effect
annotations alone.
