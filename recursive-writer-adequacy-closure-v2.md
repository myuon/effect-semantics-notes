# Recursive Writer adequacy closure v2

## Status

**Adequacy theorem obtained from one-step soundness and the fundamental
lemma.**  This removes the previous black-box assumption of “underlying PCF
adequacy.”  A concrete domain package and projective construction are fixed in
[Recursive Writer domain instance](recursive-writer-domain-instance-v2.md).

## 1. Finite return adequacy

:::{prf:theorem} Closed recursive Writer return adequacy
:label: thm-closed-recursive-writer-return-adequacy-v2

For a closed first-order computation $M:A!\rho$,

$$
M\Downarrow\mathsf{ret}(w,V)
$$

iff

$$
\llbracket M\rrbracket=\mathsf{ret}_W(w,d)
$$

for some $d$ with $V\mathcal V_A d$.
:::

:::{prf:proof}
Forward: iterate one-step soundness along the finite evaluation and use semantic
substitution.  Reverse: instantiate the closed fundamental lemma and unfold the
return clause of $\mathcal C_A^\rho$.
:::

At ground first-order types the value relation is equality with the
corresponding semantic value, so the theorem gives exact result and log.

## 2. Finite request adequacy

:::{prf:theorem} Closed recursive Writer request adequacy
:label: thm-closed-recursive-writer-request-adequacy-v2

The denotation has root

$$
\mathsf{req}_W(w;\Delta,i,p,k)
$$

iff operational evaluation exposes the same Writer prefix and nominal
operation with a related parameter and pointwise related continuation.
:::

The two directions again use one-step soundness and the request clause of the
fundamental lemma.  No global termination assumption is used.

## 3. Divergence adequacy at empty row

:::{prf:theorem} Closed recursive Writer bottom adequacy
:label: thm-closed-recursive-writer-bottom-adequacy-v2

For a closed ground computation $M:A!\varnothing$,

$$
\llbracket M\rrbracket=\bot
$$

iff deterministic evaluation is infinite and reaches neither return nor an
external boundary.
:::

:::{prf:proof}
If evaluation returned, return soundness would make the denotation nonbottom.
An unhandled new request is impossible by empty-row safety.  Conversely, if the
denotation were nonbottom, the empty-row carrier has only a Writer return, and
the fundamental lemma would reflect a finite return.  Deterministic
decomposition leaves infinite evaluation as the only case.
:::

This is a termination-sensitive adequacy theorem for the selected coarse Writer
observation.

## 4. Handler adequacy

:::{prf:theorem} Closed recursive Writer handler adequacy
:label: thm-closed-recursive-writer-handler-adequacy-v2

For a well-typed exhaustive deep handler, operational handling and the semantic
least-fixed-point handler agree on:

- every finite return observation;
- every finite residual-request observation;
- bottom versus termination when the target row is empty.
:::

The handler case of the fundamental lemma gives reflection.  The handler
equations and one-step soundness give preservation.  Deep discharge follows
independently from the target row.

## 5. What has now been discharged

The earlier recursive Writer proof assumed “computational adequacy of the
underlying recursive CBV/domain interpretation.”  It is now replaced by the
following explicit chain:

```text
CPO/domain constructors and continuity
            |
            v
admissibility of the typed logical relation
            |
            v
fundamental lemma
            |
            v
return/request reflection
            |
            v
empty-row bottom/divergence adequacy
```

No normalization theorem is used.

## 6. Remaining mathematical obligations

The proof is complete at the paper-argument level.  The domain instance page
chooses a standard countably based bifinite-domain model and reduces the
remaining infrastructure to its bilimit/closure theorems.  A fully formal proof
still needs:

1. instantiate a formal presentation of bifinite domains and its bilimit
   theorem;
2. mechanize the finite-projection admissibility induction;
3. mechanize continuity of every syntactic clause interpretation;
4. instantiate primitive base types as flat domains or provide their relation.

These are formalization obligations rather than an additional adequacy
hypothesis.

## 7. Scope of the result

This establishes adequacy for the partial Writer observation.  It does not yet
establish:

- equality of infinite Writer output traces;
- full abstraction/contextual equivalence;
- fairness or liveness;
- adequacy for nondeterministic or probabilistic recursion;
- validity of duplicating resource-sensitive resumptions.

Those require stronger observation and base packages, not changes to the
unordered row safety theorem.
