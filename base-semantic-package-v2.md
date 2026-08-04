# Base semantic package v2

## Status

**Candidate interface.** This page specifies what may be parameterized; it does not yet assert that every field is necessary.

## Separation of concerns

We represent a base effectful language by a package

$$
\mathcal B=(\mathcal L,E,T,\mathsf{Prim},\mathsf{Obs},\mathsf{Meta}).
$$

The point of a package is not maximal abstraction.  It prevents us from silently deriving runtime decomposition from a static effect algebra or from monad laws.

## Syntactic component $\mathcal L$

At minimum:

- value and computation syntax;
- fine-grain CBV evaluation contexts;
- value and computation typing;
- substitution;
- a class of base primitives;
- optionally recursion, higher-order state, or control.

The first instance remains the recursion-free [Base calculus v1](base-calculus-v1.md).

## Static effect component $E$

The weakest initial candidate is a preordered monoid

$$
(E,\otimes,I,\leq).
$$

It supports pure computation, sequencing, and subeffecting.  Additional optional capabilities are:

- finite joins $e\sqcup f$ for conditionals;
- iteration $e^*$ for loops or an unbounded number of resumptions;
- commutativity or idempotence;
- residuals or subtraction;
- pre/post indices;
- an abstraction map from intensional traces.

These must be recorded as capabilities, not assumed globally.

## Denotational component $T$

Initial candidate:

$$
T_eX
$$

is a strong $E$-graded monad with coherent weakening

$$
e\leq f\Longrightarrow T_eX\to T_fX.
$$

This supplies composition but not inspection.  If a theorem requires return/operation decomposition, it must additionally request one of:

- a free presentation;
- an interaction-tree refinement and fold;
- a resumption structure;
- a designated algebra of observable operations.

## Primitive component $\mathsf{Prim}$

For each base primitive $\beta:P_\beta\to R_\beta$ with grade $|\beta|$, provide an interpretation

$$
\llbracket\beta\rrbracket:P_\beta\to T_{|\beta|}R_\beta.
$$

Optional laws include algebraicity, naturality, strength compatibility, and equations specific to the base effect.

Whether a primitive is duplicable, discardable, commutative, or scoped must not be inferred merely from its grade.

## Observation component $\mathsf{Obs}$

Possible forms include:

- a ground observation predicate;
- a behavior-tree semantics;
- a primitive-preserving map $q:T\to O$ into an operational model;
- a simulation or logical relation between operational and denotational carriers.

Adequacy preservation can only be stated relative to one of these interfaces.

## Metatheoretic component $\mathsf{Meta}$

The base package records which results are available:

- substitution;
- preservation and progress;
- determinism or relative determinism;
- normalization or guarded recursion;
- adequacy;
- contextual equivalence;
- a fundamental logical-relations theorem.

The extension theorem should preserve selected certificates rather than re-prove an unspecified notion of “good behavior.”

## Handler capability profile

We provisionally separate five profiles.

| Profile | New capability | Expected additional base assumption |
|---|---|---|
| $C_0$ | generate and forward operations | monadic composition |
| $C_1$ | one-shot handling | exposed free layer; linear continuation use |
| $C_d$ | deep, exactly-one resumption | algebraic forwarding and stable reinstallation |
| $C_m$ | deep, zero/many resumptions | duplicable/discardable future base computation |
| $C_h$ | scoped/higher-order operations | higher-order signature and interaction laws |

This table is a research hypothesis.  “Exactly-one resumption” describes use of the captured continuation; exception-like clauses that discard it belong to a one-shot affine variant.

## Two canonical constructions to compare

### Transformer presentation

For a new signature functor $\Sigma$:

$$
\operatorname{FreeT}_{\Sigma}(T)X
\cong
T\bigl(X+\Sigma(\operatorname{FreeT}_{\Sigma}(T)X)\bigr).
$$

This is close to adding operations to an existing monadic implementation.

### Refinement-and-fold presentation

```text
intensional base/free interaction tree
                 |
                 | typed fold
                 v
          chosen base model T
```

This exposes enough structure for operational proofs without claiming that opaque $T$ can be inspected.  A major early task is to identify when these two presentations coincide and when one requires extra distributive or continuity assumptions.

## Non-goal

We do not require every effect system in the literature to instantiate one fixed record unchanged.  A useful theorem may instead quantify over a small family of packages and state explicitly where capability, protocol, or scoped-effect systems require a different interface.

