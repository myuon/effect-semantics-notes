# Research position after the v3 audit

## Revised central question

The project should ask:

> Given an already effectful language together with explicit safety, recursive
> adequacy and observation certificates, what additional obligations suffice to add
> first-order user-defined operations and exhaustive deep handlers while transporting
> those certificates, and which stronger properties provably cannot be recovered from
> an unordered free-effect row alone?

This is narrower and more testable than “how naturally can any effect system be
extended?”  It also avoids competing with known constructions by treating them as
lemmas in the transport proof.

## What we import and what we investigate

### Imported mathematical engines

- free algebra/free-monad or monad-coproduct construction for new operations;
- handler semantics as a fold/homomorphism;
- coinductive generalized resumptions and complete-Elgot iteration for recursion;
- standard row safety for exhaustive deep handling;
- standard domain/logical-relation techniques for adequacy.

We should cite and instantiate these results instead of reproving their most abstract
forms unless the exact hypotheses fail.

### Project-specific investigation

The intended theorem concerns the interfaces *between* these engines:

$$
\mathsf{BasePackage}
\xrightarrow{\operatorname{Ext}_\Sigma}
\mathsf{ExtendedPackage}.
$$

The input is not merely a monad $T$.  It contains an operational machine, a base
effect abstraction, a recursive semantic model, a relation connecting them and a
chosen observation.  The output theorem records which certificates are transported
automatically and which require new handler/base interaction laws.

## Proposed theorem architecture v4

### Theorem A: operational certificate transport

Assume a deterministic CBV base language whose internal and base steps satisfy the
base safety package.  Add a disjoint algebraic signature $\Sigma$, unordered may-row
typing and exhaustive deep handlers.

Then prove:

- deterministic decomposition into value, base step or exposed free request;
- row preservation and effect-aware progress;
- discharge of a handled interface from the outward row;
- conservativity of the old reduction relation on old programs.

This theorem is close to generic safety work.  Its role is foundational, not the
headline novelty.

### Theorem B: recursive semantic certificate transport

Assume the base model supports the iteration required by the source recursion and has
interpretations for its primitive base requests.  Form the generalized resumption
extension by $\Sigma$.

Then obtain:

- the extended monad and embedding of the base model;
- iteration/fixpoint compatibility;
- deep handlers as guarded or least-fixed-point folds;
- semantic discharge for exhaustive handlers.

Most of this theorem should be presented as an instantiation of known resumption and
handler results.  Our proof obligation is the exact alignment with Theorem A's syntax
and machine.

### Theorem C: adequacy/observation certificate transport

Assume an admissible base operational/denotational relation and a declared observation
$\mathsf{obs}$.  Lift the relation structurally through returns and $\Sigma$-requests,
and require handler clauses to preserve it.

Then prove extended soundness and the strongest observation reflection justified by
the input certificate.  The theorem must state observation levels explicitly:

- Level 1: termination/value observation;
- Level 2: base-machine observation such as Writer output or final State;
- Level 3: richer tree or contextual observation, only with a correspondingly rich
  base certificate.

The extension cannot manufacture a stronger observation theorem than the base
package supplied.

### Theorem D: interaction boundary

There is no uniform function

$$
(b,\rho,h)\longmapsto b'
$$

from an old base grade $b$, an unordered may-row $\rho$ and a handler type $h$ to an
exact post-handling base grade $b'$ for all programs and all admissible base effects.

The Writer witness is the simplest: programs with the same free row can invoke the
handled operation zero, one or multiple times, while an effectful clause emits a
different amount of log each time.  The outward row says only that invocation is
possible, not how often it occurs.  State and Exception give distinct interaction
failures.

Therefore exact base-grade preservation needs an extra certificate, such as:

- quantitative occurrence information;
- an interaction/distributive law;
- a clause-specific invariant;
- a deliberately coarse post-grade.

This negative theorem is the cleanest candidate for a genuinely project-specific
result.

## What would count as success

The work succeeds even if Theorems A--C are a disciplined synthesis of known results,
provided that it delivers:

1. one minimal, reusable package interface rather than unrelated per-language proofs;
2. an assumption matrix explaining exactly which conclusion consumes which
   certificate;
3. three materially different instances: Writer, State and Exception;
4. at least one proved impossibility/boundary theorem;
5. a comparison showing what generic effect-algebra safety and generic modular
   metatheory do not say about old semantic observations.

That would be a useful research contribution even if the algebraic carrier itself is
standard.  The paper-level claim would be “a preservation audit and boundary theorem,”
not “a new effect-handler semantics.”

## Immediate proof program

The next mathematical batch should proceed in this order:

1. replace Main theorem v3's informal premises by a single record-like
   $\mathsf{BasePackage}$ with non-circular fields;
2. factor the current proof into imported lemmas versus genuinely new glue lemmas;
3. state and prove the Writer impossibility theorem with two closed, same-typed,
   same-row programs;
4. formulate an optional $\mathsf{HandlerInteraction}$ certificate and show that it
   recovers a sound coarse or exact base-grade transformer;
5. re-run Writer, State and Exception through the same theorem statement;
6. only then decide whether a count refinement is the main positive recovery result
   or a future extension.

## Go/no-go criterion

Continue toward a paper if the package theorem contains at least one nontrivial glue
lemma not obtained merely by naming existing universal properties, and if the
interaction boundary is stated and proved at useful generality.

If the package theorem reduces completely to juxtaposing known results, retain the
notebook as a careful synthesis and pivot the research contribution to the quantitative
or handler-interaction recovery theorem.
