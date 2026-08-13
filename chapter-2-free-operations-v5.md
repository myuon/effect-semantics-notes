# Free-operation calculus: syntax, typing, and requests

Chapter II asks what is preserved when typed, user-defined operations are
adjoined to the finite language of Chapter I.  The answer is easiest to read
when three levels are kept separate.

| level | object | role | Lean status |
|---|---|---|---|
| typed source | `LanguageComp`, `LanguageStep`, exposed base/free requests | substitution, preservation, four-way progress, old-language conservativity | checked |
| finite semantic core | response trees and `FreeExtension` | bind, base embedding, structural folds and relations | checked |
| general graded theorem | $F_eA$ over $widehat E=B*\mathcal D^*$ | strength, weakening, graded base action and transport | conditional paper theorem |

The finite source tree now has an explicit Lean translation into the generic
free extension, preserving bind.  This closes the finite-level representation
gap; it does **not** identify the finite ungraded tree with the general
grade-indexed carrier.

## 1. Typed source extension

For each nominal interface $\Delta$, let

$$
\Sigma(\Delta)=\{\mathsf{op}_{\Delta,i}:P_i\to R_i\}_{i\in I_\Delta}.
$$

An operation is a computation of its response type:

$$
\frac{\Gamma\vdash V:P_i}
     {\Gamma\vdash\mathsf{op}_{\Delta,i}(V):R_i!\Delta}.
$$

The source term carries no continuation.  At runtime an evaluation context
turns $E[\mathsf{op}_{\Delta,i}(V)]$ into an exposed request whose resumption
is $r\mapsto E[\mathsf{return}\,r]$.  See [direct semantics and concrete
programs](chapter-2-operational-examples-v5.md).

For a closed well-typed term, exactly one of four cases holds: return,
internal reduction, exposed base request, or exposed free request.  Lean states
this directly as
[`HasLanguageComp.progressClosed_fourWayExactlyOne`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.HasLanguageComp.progressClosed_fourWayExactlyOne#doc).
Moreover, internal reduction preserves the base-only fragment, and every
eventual boundary of such a term is a base boundary; see
[`FinLanguageSteps.baseOnly_boundary_is_base`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.FinLanguageSteps.baseOnly_boundary_is_base#doc).

## 2. Finite semantic core

The recursion-free semantics uses response-typed trees

$$
t ::= \mathsf{ret}(a)
\mid \mathsf{base}_\beta(p,r\mapsto t_r)
\mid \mathsf{free}_{\Delta,i}(p,r\mapsto t_r).
$$

The concrete Writer/free source semantics uses `LanguageWriterTree`; the
signature-generic algebra uses `FreeExtension`.  The map
[`LanguageWriterTree.toFreeExtension`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageWriterTree.toFreeExtension#doc)
retains typed free requests and maps Writer messages to base nodes.  Its bind
law is checked by
[`toFreeExtension_bind`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.LanguageWriterTree.toFreeExtension_bind#doc).

This is the level at which Lean proves the monad laws, base embedding and
retraction, structural relator, shallow-handler naturality, and generic folds.
See [denotational free extension](chapter-2-denotational-v5.md).

## 3. General ordered theorem

The paper theorem uses the ordered effect monoid

$$
\widehat E=B*\mathcal D^*,
$$

with no exchange law between base segments and interface symbols.  Its carrier
$F_eA$ is stronger than the finite tree: it must provide graded bind, strength,
coherent weakening, and a compatible base action.  Existence of this package
is therefore an explicit hypothesis, documented in
[FreeT existence](graded-freet-existence-v1.md), rather than something inferred
from the ungraded datatype.

## 4. What the chapter proves

At the source and finite-semantic levels Lean checks:

- substitution and preservation;
- the exact four-way closed progress theorem;
- non-exposure of free requests from base-only source terms;
- finite tree bind and the bridge to the generic free extension;
- base embedding/retraction, folds, morphism lifts, and structural relations.

The fully grade-indexed extension theorem remains conditional on the strong
graded FreeT package.  Adequacy is also observation-relative: a base
observation must be extended to represent unhandled free requests.

## 5. Where this definition is used

1. [Direct semantics and concrete programs](chapter-2-operational-examples-v5.md)
   for syntax, requests, and execution examples.
2. [Denotational free extension](chapter-2-denotational-v5.md) for the finite
   core first and the graded generalization second.
3. [Preservation proofs and packages](chapter-2-main-results-v5.md) for the
   numbered statements and exact formalization boundary.
4. [Detailed proofs](chapter-2-proof-details-v5.md) for algebraic calculations.
