# Chapter I — terminology and fixed base calculus

:::{admonition} Lean correspondence — syntax and typing
:class: tip
**Lean checked.** This chapter uses [`FinLanguageVal` and `FinLanguageComp`](https://myuon.github.io/effect-semantics-notes/lean/EffectSemantics/Syntax/LanguageCalculus.html); Chapter IV separately uses `RecLanguageVal` and `RecLanguageComp`. Both instantiate one mode-indexed grammar, but `FixAllowed .finite` has no constructor, so finite terms cannot contain `fixLam`. The paper-level `BaseCert` is a readable packaging of checked component lemmas. [Full mapping](review-guide.md#chapter-i-fixed-base-language).
:::

## Status

**Foundational specification.**  No free operation, handler or fixed point is
present in this chapter.  Later chapters must state explicitly which item from
this specification they extend.

## 1. Syntactic categories

### Definition I.1 `[C1-FOUND.1.1]` — finite source syntax [[Lean: types]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageTy#doc) [[Lean: values]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FinLanguageVal#doc) [[Lean: computations]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FinLanguageComp#doc)

We use a fine-grain call-by-value calculus with separate values and
computations.

$$
\begin{aligned}
A,B ::= {}& 1 \mid \mathsf{Bool} \mid A\times B \mid A+B
          \mid A\xrightarrow{b}B,\\
V,W ::= {}& x \mid () \mid \mathsf{true}\mid\mathsf{false}
          \mid (V,W) \mid \mathsf{inl}\,V
          \mid \mathsf{inr}\,V \mid \lambda x.M,\\
M,N ::= {}& \mathsf{return}\,V
 \mid \mathbf{let}\ x\leftarrow M\ \mathbf{in}\ N\\
&\mid V\,W \mid M\,N\;\text{(derived)}
 \mid \mathbf{if}\ V\ \mathbf{then}\ M\ \mathbf{else}\ N
 \mid \mathsf{case}\ V\ \mathsf{of}\ \cdots
 \mid \beta(V).
\end{aligned}
$$

Each fixed base primitive $\beta$ has a parameter type $P_\beta$, a response
type $R_\beta$, and a declared effect upper bound $|\beta|$; applying it to a
value of type $P_\beta$ produces a computation of type $R_\beta$ at that bound.
Sums are retained at the source level; Chapter IV will not interpret
unrestricted fixed points as fixed points of every morphism in the same
bicartesian closed category.

## 2. Judgments

### Definition I.2 `[C1-FOUND.2.1]` — value and computation typing [[Lean: value typing]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageVal#doc) [[Lean: computation typing]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp#doc)

Value typing and computation typing are distinct:

$$
\Gamma\vdash V:A,
\qquad
\Gamma\vdash M:A!b,
\qquad b\in B.
$$

The base effect algebra is a preordered monoid

$$
(B,\cdot,1,\leq).
$$

The paper definition is parameterized by this preordered monoid.  The linked
Lean judgments instantiate its grades with `EffectLanguage`; their `ret`,
`letE`, and `subeffect` constructors realize the pure grade, ordered
sequencing, and weakening rules below.

`return` has grade $1$, sequencing multiplies grades in evaluation order, and
subeffecting uses $\leq$:

$$
\frac{\Gamma\vdash V:A}{\Gamma\vdash\mathsf{return}\,V:A!1},
$$

$$
\frac{\Gamma\vdash M:A!b\qquad\Gamma,x:A\vdash N:C!c}
     {\Gamma\vdash\mathbf{let}\ x\leftarrow M\ \mathbf{in}\ N:C!(b\cdot c)},
$$

$$
\frac{\Gamma\vdash M:A!b\qquad b\leq c}
     {\Gamma\vdash M:A!c}.
$$

The latent effect of a function is written over its arrow:

$$
\frac{\Gamma,x:A\vdash M:B!e}
     {\Gamma\vdash\lambda x.M:A\xrightarrow{e}B}.
$$

General computation application is the derived elaboration

```text
let f <- M in
let x <- N in
f x
```

Its effect and evaluation order follow from the core `let` and value
application rules, so no separate typing rule is required.

Branching requires a common upper bound.  If $M:A!b$, $N:A!c$, and
$b\leq d$, $c\leq d$, then both branches are weakened to $d$ before applying
the conditional rule.  A least join is convenient but not required.

Equivalently, the combined rule is

$$
\frac{
\Gamma\vdash V:\mathsf{Bool}\quad
\Gamma\vdash M:A!b\quad
\Gamma\vdash N:A!c\quad
b\leq d\quad c\leq d}
{\Gamma\vdash
\mathbf{if}\ V\ \mathbf{then}\ M\ \mathbf{else}\ N:A!d}.
$$

## 3. Operational conventions

Evaluation order is left-to-right CBV.  Evaluation contexts include

$$
E::=[]\mid \mathbf{let}\ x\leftarrow E\ \mathbf{in}\ N\mid\cdots.
$$

General application is elaborated before evaluation, so the core transition
system needs no additional administrative application contexts.

The context and the next redex/request are unique.  The base package supplies
a dedicated operational graded monad $S_b$ and an interpretation

$$
\beta^S:P_\beta\to S_{|\beta|}R_\beta.
$$

Return, sequencing and weakening are interpreted by the graded-monad
structure of $S$. Thus Writer uses an operational Writer carrier, State an
operational state transformer, Exception an operational exception carrier,
and probabilistic choice a subdistribution carrier. None of these effects is
first packed into an observation object and then wrapped in $\mathsf{Id}$.

The induced machine evaluator has the form

$$
\mathsf{run}_S(M)\in S_b\llbracket A\rrbracket
$$

for a closed $M:A!b$. Internal language reduction remains deterministic; any
branching belonging to an effect lives inside $S$. For the recursion-free
chapters the selected operational algebra must make this evaluator total on
`FinLanguageComp`.

## 4. Meaning of an effect annotation

The judgment

$$
\Gamma\vdash M:A!b
$$

means that every effect $M$ may perform is safely covered by the ordered upper
bound $b$.  It does **not** say that every execution performs all of $b$, that
$b$ is the smallest possible annotation, or that $b$ is a runtime log.

The product $b\cdot c$ records evaluation order: effects of the first
computation are placed before possible effects of its continuation.  It is a
static sequencing operation and is not assumed commutative.  The preorder
permits loss of precision.  A law such as $1\leq b$ lets a pure branch be viewed
as possibly effectful, but the exact preorder belongs to the selected base
effect system.

Runtime semantics remains an ordinary CBV transition system and does not
construct an effect word.  Soundness is supplied by the base package: each
primitive machine rule and terminal base outcome must be permitted by the
declared upper bound.

## 5. Base semantic package

A base instance supplies:

- the syntax and unique CBV decomposition;
- an operational strong graded monad $S_b$ and typed primitive maps $\beta^S$;
- the ordered upper-bound algebra $B$;
- effect soundness of its primitive machine rules;
- substitution, preservation and effect-aware progress;
- the separate grammar `FinLanguageComp`, closed under substitution and
  reduction, plus branchwise normalization for that fragment in Chapters I–III;
- a denotational strong graded monad $T_b$ and typed primitive maps $\beta^T$;
- a graded monad morphism $q:T\Rightarrow S$, or a graded logical relation,
  commuting with each primitive interpretation;
- optionally, a ground observation/pole used only after the $T$--$S$
  comparison when contextual or TT adequacy is required.

Writer, State and Exception will serve as concrete instances.  Their grades
and observations may differ; the generic theorem uses only the package laws.

## 6. Terminology fixed for later chapters

- **base effect:** an upper bound already represented by $B$ before extension;
- **free operation:** a nominal user-defined request added in Chapter II;
- **interface** $\Delta$: a typed family of free operations;
- **exposed request:** the next free request reached by CBV evaluation;
- **continuation:** the evaluation context captured at that request;
- **shallow handler:** a handler whose resumption does not reinstall itself;
- **deep handler:** the recursive reinstallation program derived in Chapter IV;
- **conservative extension:** old programs retain their typing, reductions and
  observations under the old-to-new embedding;
- **adequacy:** equality or reflection between a specified denotational and
  operational observation, never an unqualified claim.

## 7. Chapter-I obligations

Before adding operations we must prove or assume, per base instance:

1. substitution;
2. preservation;
3. unique evaluation-context/request decomposition;
4. structural closure of `FinLanguageComp` and recursion-free normalization
   sufficient to define $\mathsf{run}_S(M)$ in the operational model;
5. effect soundness: runtime steps never perform an effect excluded by the
   declared bound;
6. the selected denotational--operational comparison theorem.

These obligations are developed in order in:

- [Operational semantics and concrete machines](chapter-1-operational-examples-v5.md);
- [Denotational semantics](chapter-1-denotational-v5.md);
- [Metatheory and base certificate](chapter-1-certificate-v5.md).
