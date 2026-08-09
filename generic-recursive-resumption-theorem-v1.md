# Generic recursive resumption theorem

:::{admonition} Canonical checked abstraction
:class: tip
Every generic conclusion on this page links to its checked declaration. The principal bundle is [`GenericRecursiveResumptionCert.main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumptionCert.main#doc). Writer, State, and Exception are separate checked instances. Read the concrete Chapter-IV programs first; see the [dependency map](review-guide.md#chapter-iv-recursion-and-derived-deep-handling).
:::

## Status

**Mechanized in Lean for flat terminating observations.** This extends the
finite typed-signature construction to recursion while keeping generic facts,
base-specific obligations, and real boundaries separate.

## 1. One finite layer at a time [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.RecursiveResumptionSystem.functional#doc)

For base signature $\Sigma$, adjoined signature $\Delta$, recursive states
$X$, and results $A$, a resumption system exposes

$$s:X\longrightarrow \mathsf{Ext}_{\Sigma,\Delta}(A+X).$$

Every call exposes one finite tree. A leaf either returns or names the next
state. Given an affine shallow handler $h$, finite observer $\mathsf{obs}$,
and approximation $a:X\to O_\bot$, define

$$
\Phi_h(a)(x)=\mathsf{obs}
  ([\mathsf{inl}(v)\mapsto\mathsf{returned}(v),
    \mathsf{inr}(y)\mapsto a(y)])
  (\mathsf{shallow}_h(s(x))).
$$

The handler is reinstalled at each recursive boundary, so $\mu\Phi_h$ is the
deep behavior derived from fixpoint plus shallow handling. See
[`RecursiveResumptionSystem.functional`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.RecursiveResumptionSystem.functional#doc).

## 2. Exact observer obligations [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.RecursiveObserverContinuity#doc)

The finite observer proves two local properties:

1. increasing information assigned to leaves cannot destroy an observation;
2. an observation at an $\omega$-chain supremum already appears at a finite
   index.

They form
[`RecursiveObserverContinuity`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.RecursiveObserverContinuity#doc)
and imply continuity of $\Phi_h$ without a Writer-specific assumption.

## 3. Generic fixed-point theorem [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumptionCert.main#doc)

A recursive certificate also gives a finite-run relation and a one-layer
preserved predicate $P(x,o)$. Lean derives:

$$\Phi_h(\mu\Phi_h)=\mu\Phi_h,$$

$$\Phi_h(c)\sqsubseteq c\Longrightarrow\mu\Phi_h\sqsubseteq c,$$

$$\mathsf{Runs}(x,o)\Longleftrightarrow(\mu\Phi_h)(x)=o,$$

$$ (\mu\Phi_h)(x)=o\Longrightarrow P(x,o). $$

The checked bundle is
[`GenericRecursiveResumptionCert.main`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumptionCert.main#doc).
For the concrete instances, finite runs use the independent fuel evaluator
[`genericRunFuel`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.genericRunFuel#doc),
which executes one exposed tree and recursively evaluates leaves at smaller
fuel. Lean proves this evaluator equals the corresponding Kleene iterate.
Adequacy concerns terminating finite observations. Productive infinite traces
are bottom in this flat domain.

## 4. Morphisms, relations, and TT [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveRelationCert.lift#doc)

These transports remain distinct:

- a result map commuting with one layer commutes with the least fixed point:
  [`GenericRecursiveMorphismCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveMorphismCert.lift#doc);
- an admissible binary relation containing bottom and preserved by one layer
  relates the two least fixed points:
  [`GenericRecursiveRelationCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveRelationCert.lift#doc).
- specializing that admissible relation to a pointwise, observation-sensitive
  outcome TT relation gives
  [`GenericRecursiveOutcomeTTCert.lift`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveOutcomeTTCert.lift#doc).

The finite theorem supplies structural and TT closure inside each exposed
tree; the recursive theorem supplies admissible fixed-point closure. It does
not confuse morphisms with relations or structural closure with observational
TT closure.

## 5. Old-language conservativity [[Lean]](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumptionCert.oldLanguageConservative#doc)

If each exposed tree is `BaseOnly`, shallow handling is the identity. Hence
handled and unhandled functionals, and then their least fixed points, agree:
[`GenericRecursiveResumptionCert.oldLanguageConservative`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveResumptionCert.oldLanguageConservative#doc).

## 6. Concrete bases

Writer folds `tell` into a log. Lean proves continuity, finite/limit adequacy,
and a concrete run that handles a free request, resumes recursively, executes
`tell`, and returns `([unit], unit)`:
[`GenericRecursiveWriter.example_limit_true`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveWriter.example_limit_true#doc).
The example also proves a nontrivial recursive pole.

Exception returns `Except.error e` immediately at `raise e` and satisfies the
same generic continuity conditions:
[`GenericRecursiveException.limit_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveException.limit_adequacy#doc).

State cannot be observed without an initial store. Its honest finite outcome
is therefore

$$\mathsf{Bool}\to\mathsf{Option}(A\times\mathsf{Bool}).$$

The mechanized observer handles `get` and `put`; `toggleTree` is checked from
both stores. For `get`, the proof takes finite witnesses for the `false` and
`true` continuations and transports both to their maximum index. This closes
recursive continuity and yields
[`GenericRecursiveState.limit_adequacy`](https://myuon.github.io/effect-semantics-notes/lean/find/?pattern=EffectSemantics.GenericRecursiveState.limit_adequacy#doc).

## 7. Boundary

Covered: typed algebraic signatures, finite exposed layers, affine shallow
handlers reinstalled through recursion, terminating adequacy, outcome maps,
admissible relations, and old-language conservativity.

Not covered: automatic signature extraction from an opaque monad, full
abstraction, productive infinite output, and higher-order/non-algebraic
operations. These require genuinely additional structure.
