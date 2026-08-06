# Finite shallow structure-preservation theorem v4

## Status

**General theorem extracted from the Writer, State and Exception instances;
paper-level proof.**  It deliberately separates unconditional finite-tree
results from conclusions requiring a denotational base certificate.

## 1. Assumptions

Let $B$ be a `FiniteBasePackage` and let $\Sigma$ be a finite family of nominal
first-order free interfaces.  Assume:

- **F1 — typed deterministic decomposition:** every closed well-typed base
  computation is a value, takes a unique internal/base step, or exposes one
  classified old terminal outcome;
- **F2 — finite base evaluation:** base evaluation has no infinite reduction;
- **F3 — substitution and residual typing:** value and captured-context
  substitution preserve typing;
- **F4 — disjointness:** new constructors add no reduction rule whose source is
  an old term;
- **F5 — base transparency during search:** an old step can be propagated under
  the pending shallow matcher without changing which new interface it names;
- **F6 — separated free requests:** returns, old outcomes and nominal free
  requests are distinct operational observations;
- **F7 — exhaustive typed responses:** every operation of the named interface
  has one response clause of its declared response type.

For semantic adequacy, additionally assume:

- **F8 — base observation certificate:** explicit finite base behavior trees
  fold into a model $T$, and the supplied relation reflects the chosen ground
  observation;
- **F9 — compatible clauses:** each response clause is related to its tree
  denotation under related substitutions.

No CPO, admissibility or fixed-point assumption is needed.

## 2. Extension structure

Let $\mathsf{FTree}_{B+\Sigma}A$ be the well-founded typed behavior trees with
return, old-base and new-free nodes.  Row refinement selects trees whose free
node labels lie in $\rho$:

$$
\mathsf{FTree}_{B+\Sigma,\rho}A.
$$

:::{prf:theorem} Finite free-extension structure
:label: thm-finite-free-extension-structure-v4

Under F1--F7, the extended recursion-free calculus has:

1. a row-refined finite free-tree monad;
2. a monad embedding of the old finite behavior trees at row $\varnothing$;
3. functorial weakening along $\rho\subseteq\rho'$;
4. a canonical lifting of primitive-preserving base-tree morphisms;
5. a structural lifting of return/bind-compatible base relations.
:::

**Proof sketch.**  Return is a leaf and bind replaces every return leaf by a
tree.  The monad laws follow by well-founded induction.  Row soundness follows
because leaf replacement introduces only labels from the bound continuation
row.  A base morphism or relation is extended homomorphically over each new
free node.  No handler equation is used in this proof.

## 3. Operational preservation

:::{prf:theorem} Finite shallow operational preservation
:label: thm-finite-shallow-operational-v4

Under F1--F7, adding free operations and the intended shallow matcher provides:

1. deterministic decomposition into return, step, old outcome or exposed free
   request;
2. value-type and unordered-row preservation;
3. effect-aware progress;
4. termination relative to terminating response clauses;
5. exact operational conservativity on old syntax.
:::

**Proof sketch.**  Induct on the finite base evaluation and then invert the
unique first free boundary.  `S-Ret`, `S-Match` and `S-Other` are disjoint.
For `S-Match`, response substitution gives an $R_i$ computation and residual
typing plugs the returned response into the captured context.  The measure is
the remaining base evaluation plus the finite syntax/tree size; matching
removes the current free node and does not reinstall the matcher.  Old terms
cannot use a new rule by F4.

The termination clause requires response clauses themselves to belong to the
same recursion-free fragment.  They may emit further free requests, which are
terminal boundaries rather than divergence.

## 4. Handler/tree correspondence

:::{prf:theorem} First-boundary correspondence
:label: thm-first-boundary-correspondence-v4

For every closed typed computation $M$,

$$
\mathsf{beh}(\mathsf{shallow}_\Delta(M,h))
=
\mathsf{sh}_{\Delta,h}(\mathsf{beh}(M)).
$$
:::

**Proof sketch.**  Induct through the finite sequence of old base boundaries.
At the first new boundary, use exactly one of the return, matching-interface or
different-interface equations.  In the matching case, substitution semantics
identifies the operational

$$
\mathbf{let}\ r\leftarrow H_i\ \mathbf{in}\ E[\mathsf{return}\;r]
$$

with tree bind $\llbracket H_i\rrbracket\mathbin{\gg=}k$.  Neither side recursively
handles $k$.

## 5. Adequacy transport

:::{prf:theorem} Finite shallow adequacy transport
:label: thm-finite-shallow-adequacy-v4

Under F1--F9, the structural lifting of the base relation contains every
well-typed extended term.  Hence the extended tree/model semantics is adequate
for the same ground observation level supplied by F8, including computations
containing the shallow matcher.
:::

**Proof sketch.**  The fundamental lemma is a structural induction on typing.
The new operation case follows from the free-node clause of the lifted
relation.  The shallow case uses first-boundary correspondence and F9.  Ground
reflection is not reproved: it is inherited from F8 after distinguishing free
requests using F6.

This theorem transports the chosen observation; it does not strengthen it.
For example, a base certificate observing only final State cannot suddenly
yield equality of the entire state-access trace.

## 6. Exact limits

:::{prf:proposition} No general shallow discharge from unordered rows
:label: prop-no-shallow-row-discharge-v4

There is no sound general typing rule

$$
\rho\cup\{\Delta\}
\xrightarrow{\mathsf{shallow}_\Delta}
\rho
$$

for the intended matcher.
:::

**Witness.**  The program performs two sequential $\Delta$ operations.  The
matcher replaces the first response and its bare continuation immediately
exposes the second.  Both occurrences collapse to the same may-row label.

:::{prf:proposition} The shallow transformation is not generally a monad morphism
:label: prop-shallow-not-monad-morphism-v4

There is no general law saying that $\mathsf{sh}_{\Delta,h}$ preserves bind.
:::

**Witness.**  Let $M$ be one matching $\Delta$ request and let $f$ perform a
second matching $\Delta$ request.  Then

$$
\mathsf{sh}(M\mathbin{\gg=}f)
$$

handles the request in $M$ and leaves the request in $f$ exposed, whereas the
monad-morphism right-hand side

$$
\mathsf{sh}(M)\mathbin{\gg=}(\mathsf{sh}\circ f)
$$

installs a fresh matcher for $f$ and handles both.  Thus the ordinary
monad-morphism bind equation fails.

:::{prf:proposition} No exact old-grade transformer from row data alone
:label: prop-no-exact-old-grade-shallow-v4

An aggregate old grade $b$, unordered row $\rho$ and clause grade $c$ do not in
general determine the exact old grade after shallow matching.
:::

**Witnesses.**  Writer distinguishes the insertion position of clause output;
State lets the clause change what the tail reads; Exception can abort before,
inside or after the match.  An exact theorem therefore requires a positional
trace, an interaction/distributive law, a more informative grade, or a coarse
join that safely forgets the difference.

## 7. What Chapter I has established

The finite shallow extension preserves the **language infrastructure**:

$$
\text{typing}
+\text{decomposition}
+\text{finite free monad}
+\text{relations}
+\text{declared adequacy}.
$$

The handler itself preserves a narrower structure:

$$
\text{typed first-boundary behavior}
+\text{operational/tree correspondence}.
$$

It does not preserve arbitrary sequencing algebra, erase a may-row label, or
compute an exact old effect summary.  These are not failures of the effect
system: they state precisely how much information an unordered may-row and a
one-boundary handler expose.

Chapter II can now ask separately which changes come from replacing finite
trees by recursive resumptions, and which are repaired by replacing shallow
matching with deep reinstallation.
