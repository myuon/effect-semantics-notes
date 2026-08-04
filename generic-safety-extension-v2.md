# Generic safety extension v2

## Status

**First generic theorem candidate extracted from four concrete bases.** The
proof is on paper and parameterizes only the operational safety layer.  It does
not claim a precise transformation of the old base effect annotation.

## 1. Input interface: `BaseSafety`

Fix a fine-grain CBV base language with values, computations, typing, and
runtime configurations

$$
\langle\xi,M\rangle,
$$

where $\xi$ is arbitrary base runtime data.

Assume the following.

### BS-1: syntactic infrastructure

Value substitution and residual evaluation-context typing hold for the base
calculus.

### BS-2: classified deterministic decomposition

Every closed, well-typed base configuration uniquely:

- returns a value;
- takes one deterministic step;
- exposes one typed base-specific nonreturn outcome $o$.

The outcome class may be empty.  Writer and State use no terminal base outcome;
Exception uses `raise`.

### BS-3: base preservation

Base steps preserve value type and the old base typing information.  Typed base
outcomes are stable under the old base contexts that do not handle them.

### BS-4: new-row silence

Every old base term and primitive is assigned empty **new** free-effect row.

### BS-5: handler contextuality

A base internal step under a pending new free handler lifts to a step with the
same pending handler.  A base nonreturn outcome propagates according to the old
base rules and is not mistaken for a new free request.

### BS-6: conservative syntax

The new rules do not rewrite a term consisting solely of old syntax, except by
lifting an old step through a context that itself uses new syntax.

These assumptions make no reference to a base monad, base effect monoid, or
precise base grade.

## 2. Extension construction

For a finite family of nominal first-order signatures $\Sigma$, extend the
base calculus with:

- invocations $\operatorname{op}_{\Delta,i}(V)$;
- finite unordered new-effect rows $\rho$;
- exhaustive deep handlers from [Common free-handler calculus
  v2](common-free-handler-calculus-v2.md).

The old typing judgment is paired with or projected alongside

$$
\Gamma\vdash M:A!\rho.
$$

At this layer only the new row is transformed by the handler.

## 3. Extended decomposition

:::{prf:theorem} Generic extended decomposition
:label: thm-generic-safety-decomposition-v2

Under BS-1--BS-6, every closed, well-typed extended configuration uniquely:

1. returns a value;
2. takes one deterministic step;
3. exposes one old base-specific nonreturn outcome;
4. exposes one unhandled new free request with its maximal transparent
   context.
:::

:::{prf:proof}
Induction on the unique extended CBV evaluation context.

- Old active forms use BS-2.
- A new operation is a request unless the nearest handler has its interface.
- A matching exhaustive handler gives one `H-Op-Deep` redex.
- A nonmatching handler extends the request's transparent context.
- A base step lifts through a new handler by BS-5.
- A base nonreturn outcome remains in the base-outcome class unless an old base
  construct handles it.

Nominal decidable matching and maximal transparent contexts make the cases
unique and disjoint.
:::

:::{prf:corollary} Relative determinism
:label: cor-generic-safety-determinism-v2

If the base transition is deterministic, the extended one-step transition is
deterministic.
:::

## 4. Generic new-row preservation

:::{prf:theorem} Generic free-row preservation
:label: thm-generic-row-preservation-v2

If

$$
\Gamma\vdash M:A!\rho
$$

and

$$
\langle\xi,M\rangle\to\langle\xi',M'\rangle,
$$

then

$$
\Gamma\vdash M':A!\rho.
$$
:::

:::{prf:proof}
By cases on the step.

- Old steps preserve the empty new-row projection by BS-3 and BS-4.
- Ordinary beta and sequencing use BS-1.
- Handler return uses value substitution.
- Handler matching uses parameter substitution and residual-context typing to
  type the inserted deep resumption.
- Context cases reconstruct the surrounding typing rule.
- Subeffecting restores the displayed upper row.
:::

The proof never computes the transformed old base grade.  A concrete combined
typing theorem may need extra premises for that component.

## 5. Progress and empty-row safety

:::{prf:theorem} Generic effect-aware progress
:label: thm-generic-progress-v2

A closed, well-typed extended computation either:

- returns;
- steps;
- exposes a typed old base outcome;
- exposes a new free request whose interface belongs to its outward row.
:::

:::{prf:proof}
Use extended decomposition.  Invert projected row typing in the free-request
case.  Old base outcomes are classified separately and therefore do not require
a new interface label.
:::

:::{prf:corollary} Generic empty-new-row safety
:label: cor-generic-empty-row-v2

A closed computation with new row $\varnothing$ cannot be blocked on an
unhandled newly added operation.  It may still exhibit a permitted old base
outcome.
:::

## 6. Generic deep discharge

:::{prf:theorem} Generic deep discharge
:label: thm-generic-deep-discharge-v2

Suppose an exhaustive deep handler for $\Delta$ is checked with outward new row
$\omega$ and $\Delta\notin\omega$.  Then no execution of the handled term
exposes an unhandled $\Delta$ request.
:::

:::{prf:proof}
`T-Handle` assigns the outward row $\omega$.  Generic preservation maintains it
at every step.  Generic progress would require any exposed $\Delta$ request to
satisfy $\Delta\in\omega$, a contradiction.

Operationally, matching continuations reinstall the handler and nonmatching
requests retain it in their forwarded continuations.  The premise also excludes
new $\Delta$ requests produced directly by clauses.
:::

This theorem is the precise unordered-row sense in which a deep handler is an
eliminator.

## 7. Generic conservativity

:::{prf:theorem} Generic old-language conservativity
:label: thm-generic-language-conservativity-v2

An old term containing no new operation or new handler has exactly its old
steps and old observations in the extension, and its projected new row is
empty.
:::

:::{prf:proof}
By BS-4 and BS-6.  Induction on the old evaluation preserves the absence of new
syntax.
:::

:::{prf:theorem} Qualified identity-handler inertness
:label: thm-generic-handler-inertness-v2

An identity-return new handler around a base-only computation preserves its old
observable behavior if old steps and outcomes propagate through that pending
handler and no operation clause is reachable.
:::

A nonidentity return clause invalidates this statement in Writer and State, so
identity return or an observation-preserving return algebra is necessary.

## 8. Optional semantic layer

The safety theorem above is operational.  To obtain a generic handler fold and
adequacy theorem, additionally assume `BaseResumptionModel`:

1. an intensional carrier $\mathsf{Res}_{T,\Sigma}A$ exposing returns, typed old
   nonreturn outcomes, and new free requests with continuations;
2. interpretations of base steps and outcomes;
3. a structural deep-handler fold;
4. an observation map related to the base operational outcomes.

Then the Writer, State, and Exception proofs share the following scheme.

:::{prf:conjecture} Generic resumption soundness
:label: conj-generic-resumption-soundness-v2

Every extended operational step preserves the resumption denotation, and the
deep operational handler commutes with the structural handler fold.
:::

:::{prf:conjecture} Conditional generic adequacy
:label: conj-generic-resumption-adequacy-v2

For closed first-order computations that reach a classified outcome, the
operational outcome agrees with the outer constructor and observation of the
resumption denotation, and conversely.
:::

These remain conjectures until `BaseResumptionModel` is stated with enough
coherence to make the proof independent of the three concrete presentations.

## 9. What this theorem intentionally omits

The theorem does not provide:

- a precise post-handler old base grade;
- a guarantee that multi-shot resumption is valid for linear resources;
- commutation of old and new handlers;
- normalization of unrestricted clauses;
- a construction of $\mathsf{Res}_{T,\Sigma}$ for every opaque monad $T$.

Writer, State, and Exception give counterexamples or distinct choices for these
claims.  They belong to `HandlerInteraction` and `BaseEffectAbstraction`, not to
the generic safety layer.

## 10. Current theorem boundary

At this point the positive result is:

> A base language with deterministic classified operational behavior and
> ordinary substitution/contextuality admits a conservative unordered
> free-operation extension with exhaustive deep discharge at the projected row
> level.

The next nonautomatic question is:

> What additional abstraction of occurrence, order, and scope gives a useful
> sound transformer for the old base effect annotation?

That question cannot be answered uniquely from the four examples and is the
current design fork.
