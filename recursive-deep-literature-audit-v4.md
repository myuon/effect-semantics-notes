# Chapter II literature audit: recursion, operations, handlers and adequacy

## Status

**Primary-source audit completed for the semantic architecture used below.**
This page records what is imported from prior work and what remains specific to
our extension question.  It does not claim that the bibliography is exhaustive.

## 1. Plotkin and Power: recursive algebraic effects without handlers

[Adequacy for Algebraic Effects](https://homepages.inf.ed.ac.uk/gdp/publications/Op_Sem_Comp_Lam.pdf)
studies call-by-value PCF with algebraic operations, both without and with
general recursion.

For recursion, operational behavior is a possibly infinite, finitely branching
effect tree.  Denotationally, finite and infinite behaviors inhabit a free
continuous algebra.  The semantic category and monad are order-enriched;
recursion is interpreted by the usual least fixed point.  Their main recursive
adequacy theorem identifies the denotation of a program with the homomorphic
interpretation of its operational effect tree.

What we import:

- recursion turns finite effect trees into partial or infinitary trees;
- continuity and least fixed points support ordinary general recursion;
- adequacy can be factored through the operational effect tree;
- the chosen algebra of observations determines the final adequacy statement.

What it does not directly provide for us:

- a source effect-handler construct;
- deep reinstallation and handler clauses;
- transport from a separately supplied, already effectful base language.

## 2. Plotkin and Pretnar: recursive handler semantics

Section 7 of
[Handling Algebraic Effects](https://lmcs.episciences.org/705/pdf)
sketches the recursive extension of their algebraic treatment of handlers.
They add an operation `div` denoting nontermination, replace equations by
inequations with `div` least, move from `Set` to $\omega$Cpo, use continuous
free-model functors, and interpret the recursion construct by a least fixed
point.

Handlers remain homomorphisms into models of the effect theory.  Correct
handlers are strict and therefore cannot redefine divergence.  This gives the
right algebraic reading of recursion plus handlers, but the section is a
semantic sketch rather than the operational adequacy proof we need.

What we import:

- divergence must be part of the ordered theory/model;
- handler interpretation must be continuous and strict at bottom;
- least-fixed-point recursion and algebraic handler interpretation must agree.

## 3. Bauer and Pretnar: the closest complete calculus theorem

[An Effect System for Algebraic Effects and Handlers](https://lmcs.episciences.org/1153/pdf)
is the closest complete predecessor.

Core Eff has first-class operations and deep handlers.  Operationally, a
handler wraps itself around the continuation, so later matching operations are
handled again.  Its computation domain is the minimal solution of

$$
D
\cong
\left(A+\coprod_i P_i\times(R_i\to D)\right)_\bot.
$$

Elements are potentially non-well-founded operation trees.  Function,
computation and handler types form a larger recursive domain system.  A handler
is defined by strict continuous recursion over the computation domain:

- bottom maps to bottom;
- a return uses the value clause;
- an operation uses the matching clause, passing the recursively handled
  continuation, or forwards it with that handled continuation.

Recursive functions are interpreted by least fixed points.  Pitts's minimal
invariant relations supply both:

1. an admissible semantic subset validating the effect annotation; and
2. an admissible formal-approximation relation between denotations and closed
   programs.

The fundamental lemma includes both the handler case and the recursive-function
case.  Their adequacy corollary says, in particular, that a closed unit
computation whose denotation is a returned unit operationally returns unit;
the surrounding discussion also reflects non-bottom operation boundaries.

Important differences from our project:

- core Eff builds one handler language and one global operation-tree model;
- its denotation factors through skeletal types and treats effect information
  extrinsically;
- it does not take an existing Writer, State or Exception adequacy certificate
  as input and state exactly which certificate fields survive an extension;
- it does not promise exact transformation of an independent old base grade.

Thus we should reuse its domain and logical-relation proof pattern, not claim
that pattern as new.

## 4. Coinductive generalized resumptions

[Unguarded Recursion on Coinductive Resumptions](https://arxiv.org/abs/1405.0854)
starts with a monad $T$ for base effects and adjoins free operations through the
coinductive generalized resumption transformer

$$
T_\Sigma A
\cong
\nu X.\,T(A+\Sigma X).
$$

If $T$ is a complete Elgot monad, the transformer has a unique complete-Elgot
iteration extending that of $T$.  It is characterized as freely adjoining the
signature in the category of complete Elgot monads.

This is a nearly exact match for our **recursive carrier and iteration layer**.
It does not by itself give:

- source typing or operational safety;
- an effect-row discharge theorem;
- a deep handler for arbitrary effectful clauses;
- computational adequacy for a selected base observation.

Complete-Elgot structure says how recursive equations are solved; it does not
say that the chosen solution reflects the operational observations of a
particular programming language.

## 5. Later adequacy work

[Adequacy for Algebraic Effects Revisited](https://doi.org/10.1145/3720457)
gives a modern interaction-tree operational semantics and monad/algebra
denotational semantics for a broad class of algebraic effects, including
infinitary signatures, with a logical-relations adequacy proof.  It reinforces
the methodology of factoring adequacy through interaction trees.  The theorem
we require still has the additional obligations of deep handler
reinstallation, general recursion and a separately supplied base-effect
observation package.

## 6. Audit conclusion

The following Chapter II ingredients are prior art:

| ingredient | status |
|---|---|
| partial/infinitary operation trees | established |
| least-fixed-point interpretation of recursive functions | established |
| deep handlers as strict continuous recursive maps | established |
| admissible logical relations for recursive handler calculi | established |
| recursive handler-language ground adequacy | established in core Eff |
| free extension of a complete-Elgot base monad | established |

Our reconstruction should therefore target the interface between them:

> given an already effectful base machine/model/relation/observation package,
> construct its free recursive resumption extension, install exhaustive deep
> handlers, and state exactly which old certificates are transported and which
> handler/base interaction laws remain additional assumptions.

This is the claim tested by the concrete instances and theorem below.
