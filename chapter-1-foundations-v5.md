# Chapter I — terminology and fixed base calculus

## Status

**Foundational specification.**  No free operation, handler or fixed point is
present in this chapter.  Later chapters must state explicitly which item from
this specification they extend.

## 1. Syntactic categories

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

Here $\beta:P_\beta\to R_\beta$ ranges over the fixed base primitives.  Sums
are retained at the source level; Chapter IV will not interpret unrestricted
fixed points as fixed points of every morphism in the same bicartesian closed
category.

## 2. Judgments

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

General CBV application evaluates the function, then the argument, then the
function body:

$$
\frac{
\Gamma\vdash M:(A\xrightarrow{e}B)!e_M
\qquad
\Gamma\vdash N:A!e_N
}{
\Gamma\vdash M\,N:B!(e_M\cdot e_N\cdot e)
}.
\tag{T-App}
$$

In the fine-grain core this is the elaboration

```text
let f <- M in
let x <- N in
f x
```

so the displayed order is not a convention imposed after the fact.

Each primitive has a declared bound:

$$
\frac{\beta:P_\beta\to R_\beta\qquad\Gamma\vdash V:P_\beta}
     {\Gamma\vdash\beta(V):R_\beta!|\beta|}.
$$

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

The context and the next redex/request are unique, but a base request may have
more than one response.  A base package therefore supplies a response monad
$\mathcal K$ and

$$
\mathsf{resp}_\beta:P_\beta
\to\mathcal K(R_\beta+\mathsf{Out}_\beta).
$$

$\mathcal K=\mathsf{Id}$ gives deterministic primitives,
$\mathcal K=\mathcal P$ gives nondeterministic choice, and
$\mathcal K=\mathsf{SubDist}$ gives probabilistic choice.  The induced machine
step is a kernel

$$
\mathsf{step}_B:\mathsf{Conf}
\to\mathcal K(\mathsf{Conf}+\mathsf{Out}_B).
$$

For the recursion-free chapters we require every branch in the support of this
kernel to be well founded.  We do not require the response itself to be unique.

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

- the syntax, unique CBV decomposition, and response monad $\mathcal K$;
- typed response maps $\mathsf{resp}_\beta$ and their induced kernel;
- the ordered upper-bound algebra $B$;
- effect soundness of its primitive machine rules;
- substitution, preservation and effect-aware progress;
- recursion-free branchwise normalization for Chapters I–III;
- an observation function $\mathsf{obs}_B$;
- optionally a graded monad $T_b$ and an adequacy certificate relating
  denotation to $\mathsf{obs}_B$.

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
4. recursion-free branchwise normalization and a well-defined outcome object
   in $\mathcal K(\mathsf{Obs}_B)$;
5. effect soundness: runtime steps never perform an effect excluded by the
   declared bound;
6. the selected denotational adequacy statement.

These obligations are developed in order in:

- [Operational semantics and concrete machines](chapter-1-operational-examples-v5.md);
- [Denotational semantics](chapter-1-denotational-v5.md);
- [Metatheory and base certificate](chapter-1-certificate-v5.md).
