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
A,B ::= {}& 1 \mid A\times B \mid A+B \mid A\to(B!b),\\
V,W ::= {}& x \mid () \mid (V,W) \mid \mathsf{inl}\,V
          \mid \mathsf{inr}\,V \mid \lambda x.M,\\
M,N ::= {}& \mathsf{return}\,V
 \mid \mathbf{let}\ x\leftarrow M\ \mathbf{in}\ N\\
&\mid V\,W \mid \mathsf{case}\ V\ \mathsf{of}\ \cdots
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

The precise conditional join is supplied by the base package.  It may be a
join in $B$ or, more generally, union after interpreting grades as trace
languages.

## 3. Operational conventions

Evaluation is deterministic left-to-right CBV.  Evaluation contexts include

$$
E::=[]\mid \mathbf{let}\ x\leftarrow E\ \mathbf{in}\ N\mid\cdots.
$$

The base package supplies transition rules for $E[\beta(V)]$.  A closed,
well-typed computation either takes a step or is a classified base outcome.
For the recursion-free chapters we additionally require that evaluation is
well founded.

## 4. Runtime traces and static effects

We distinguish three levels.

1. A **runtime event** is one observable base action performed in one step.
2. A **runtime behavior** is an ordered sequence of events together with its
   current exit: ordinary return or a classified base abort.
3. A **static effect** is a compositional description of the possible behaviors
   of a term before execution.

Write a behavior as $(t,q)$, where $t$ is an event word and

$$
q::=\checkmark\mid\mathsf{abort}(a).
$$

Sequential composition is completion-sensitive:

$$
(t,\checkmark)\mathbin{;} (u,q)=(t\cdot u,q),
$$

$$
(t,\mathsf{abort}(a))\mathbin{;} (u,q)
=(t,\mathsf{abort}(a)).
$$

It extends pointwise to behavior languages.  The unit is
$\{(\epsilon,\checkmark)\}$.  For Writer and total State every behavior exits
with $\checkmark$, so this reduces to ordinary trace concatenation.  The exit
component is essential for Exception: effects after a raise are not executed.

For each $b\in B$, let $\mathcal L_B(b)$ be its behavior-language interpretation.  The
minimum soundness requirements are

$$
(\epsilon,\checkmark)\in\mathcal L_B(1),
$$

$$
\mathcal L_B(b)\mathbin{;}\mathcal L_B(c)
\subseteq
\mathcal L_B(b\cdot c),
$$

$$
b\leq c\Longrightarrow\mathcal L_B(b)\subseteq\mathcal L_B(c).
$$

Exact models may replace the inclusion in sequencing by equality.  This
separation lets a type effect remain an upper approximation while still
retaining event order.

## 5. Base semantic package

A base instance supplies:

- the syntax and deterministic machine above;
- the ordered algebra $B$ and trace interpretation $\mathcal L_B$;
- substitution, preservation and effect-aware progress;
- recursion-free normalization for Chapters I–III;
- an observation function $\mathsf{obs}_B$;
- optionally a graded monad $T_b$ and an adequacy certificate relating
  denotation to $\mathsf{obs}_B$.

Writer, State and Exception will serve as concrete instances.  Their event
alphabets and observations differ, so no theorem may identify their traces
without an explicit abstraction map.

## 6. Terminology fixed for later chapters

- **base effect:** an effect already represented by $B$ before extension;
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
3. deterministic decomposition;
4. recursion-free normalization;
5. trace soundness
   $\mathsf{trace}(M)\in\mathcal L_B(b)$ for $M:A!b$;
6. the selected denotational adequacy statement.

These obligations are developed in order in:

- [Operational semantics and concrete machines](chapter-1-operational-examples-v5.md);
- [Denotational semantics](chapter-1-denotational-v5.md);
- [Metatheory and base certificate](chapter-1-certificate-v5.md).
