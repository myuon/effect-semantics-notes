# Generic resumption extension v2

## Status

**Main denotational theorem candidate for the unordered-row version.** The
construction is standard in shape; the research claim concerns the complete
property-preservation package and its separation from base-grade precision.

## 1. Input data

Work in `Set` for the first theorem.  Fix:

1. a base monad $(T,\eta^T,\mathbin{\gg=_T})$;
2. a first-order signature functor

   $$
   \Sigma X=
   \sum_{\Delta\in\mathcal D}
   \sum_{i\in I_\Delta}P_i\times(R_i\to X);
   $$

3. for every set $A$, an initial algebra (hence a chosen initial solution) of

   $$
   X\cong T(A+\Sigma X).
   $$

The third assumption is the required existence condition.  Here “initial” is
essential: an arbitrary fixed point of the displayed equation does not supply
the structural recursion used below.  The condition holds for the
well-founded concrete trees used for Pure, Writer, State, and Exception.  We do
not assert it for every large or nonaccessible monad/signature combination.

Write the solution as

$$
\mathsf{Res}_{T,\Sigma}A
$$

with destructor

$$
\mathsf{out}:
\mathsf{Res}_{T,\Sigma}A
\to
T(A+\Sigma(\mathsf{Res}_{T,\Sigma}A)).
$$

This is the free-operation transformer over the already effectful base $T$.

## 2. Canonical embedding and operations

There is a canonical lift

$$
\mathsf{lift}_T:TA\to\mathsf{Res}_{T,\Sigma}A
$$

obtained by mapping each base return into the left return summand and folding
into the initial solution.

The new operation

$$
\operatorname{op}_{\Delta,i}:P_i
\to\mathsf{Res}_{T,\Sigma}R_i
$$

is one free request node with a pure response continuation.

:::{prf:theorem} Canonical unordered free extension
:label: thm-generic-free-resumption-v2

Assuming the initial solutions above, $\mathsf{Res}_{T,\Sigma}$ is a monad,
$\mathsf{lift}_T$ is a monad morphism, and the displayed operations are
algebraic operations of that monad.
:::

:::{prf:proof}
Unit injects an $A$ value through $\eta^T$ into the return summand.  Bind is the
unique structural map that:

- replaces a return by the supplied continuation;
- composes through the outer $T$ layer using its bind;
- preserves every free request and binds recursively in its response
  continuation.

The monad laws follow by initiality/structural induction and the monad laws of
$T$.  The same equations show that $\mathsf{lift}_T$ preserves unit and bind.
An operation is algebraic because postcomposition by bind acts only on its
response continuation.
:::

## 3. Unordered row refinement

For a finite row $\rho\subseteq\mathcal D$, let

$$
\Sigma_\rho X=
\sum_{\Delta\in\rho}
\sum_{i\in I_\Delta}P_i\times(R_i\to X).
$$

Define

$$
\mathsf{Res}_{T,\rho}A
$$

using $\Sigma_\rho$.  Inclusion $\rho\subseteq\sigma$ induces a canonical
weakening

$$
\mathsf{wk}_{\rho,\sigma}:
\mathsf{Res}_{T,\rho}A
\to
\mathsf{Res}_{T,\sigma}A.
$$

:::{prf:theorem} Row-refined monad structure
:label: thm-generic-row-resumption-v2

The family satisfies

$$
\eta:A\to\mathsf{Res}_{T,\varnothing}A,
$$

$$
\mathsf{Res}_{T,\rho}A\times
(A\to\mathsf{Res}_{T,\sigma}C)
\to
\mathsf{Res}_{T,\rho\cup\sigma}C,
$$

with coherent proof-irrelevant weakening by row inclusion.
:::

The row is a may-bound.  It records neither the number nor the order of request
nodes.

## 4. Deep handler algebra

Split the input signature into the handled interface and residual signature:

$$
\Sigma_{\rho\cup\{\Delta\}}
\cong
\Sigma_\rho+\Sigma_\Delta,
\qquad
\Delta\notin\rho.
$$

Fix target row $\omega$ with $\rho\subseteq\omega$.  A handler from $A$ to $C$
provides:

$$
r:A\to\mathsf{Res}_{T,\omega}C
$$

and

$$
c_i:
P_i\to
(R_i\to\mathsf{Res}_{T,\omega}C)
\to
\mathsf{Res}_{T,\omega}C
$$

for every operation in $\Delta$.

:::{prf:theorem} Generic deep-handler fold
:label: thm-generic-deep-fold-v2

There is a unique structural handler

$$
H_{\Delta,h}:
\mathsf{Res}_{T,\rho\cup\{\Delta\}}A
\to
\mathsf{Res}_{T,\omega}C
$$

that:

1. sends a base-layer return to $r$;
2. sends a matching request to $c_i$ with recursively handled resumption;
3. forwards a residual request and recursively handles its continuation;
4. preserves the outer base $T$ behavior through $\mathsf{lift}_T$ and bind.
:::

:::{prf:proof}
Use initiality of the source resumption object.  After exposing one outer $T$
layer, lift that layer into the target resumption monad and bind with the case
map on return, residual request, or matching request.  Recursive occurrences
appear only in request continuations.  The resulting equations specialize to
the Writer, State, and Exception folds already calculated.
:::

Clause results are not passed through $H_{\Delta,h}$ again.  Only the captured
resumption is.  Thus the fold has standard deep scope: it handles the entire
resumed source computation but does not automatically catch a fresh $\Delta$
emitted directly by a clause.

## 5. Denotational discharge

:::{prf:corollary} Generic denotational discharge
:label: cor-generic-denotational-discharge-v2

If $\Delta\notin\omega$, then the result of $H_{\Delta,h}$ contains no free
$\Delta$ request.
:::

This is structural: matching source nodes are replaced, residual nodes have
different labels, and clause results are $\Delta$-free by their target row.

## 6. Base conservativity

:::{prf:theorem} Denotational base embedding
:label: thm-generic-denotational-conservativity-v2

The map

$$
\mathsf{lift}_T:TA\to\mathsf{Res}_{T,\varnothing}A
$$

preserves return and sequencing.  Interpreting an old term in the extension is
its old $T$ denotation followed by $\mathsf{lift}_T$.
:::

This is denotational conservativity as an embedding, not necessarily a carrier
isomorphism.  The extended carrier contains new request trees absent from $T$.

If a new handler has an observation-preserving return algebra, then applying it
to an embedded base-only computation preserves the chosen observation.  For a
literal identity result type and identity return clause, the fold restricts to
the lifted base computation.

## 7. Lifting base morphisms

Let

$$
q:T\Rightarrow U
$$

be a monad morphism.  Assume both resumption solutions exist.

:::{prf:theorem} Resumption morphism lifting
:label: thm-generic-resumption-morphism-v2

There is a canonical natural transformation

$$
\widehat q:
\mathsf{Res}_{T,\rho}
\Rightarrow
\mathsf{Res}_{U,\rho}
$$

that applies $q$ to each exposed base layer and recursively preserves free
requests.  It is a monad morphism, commutes with row weakening, and satisfies

$$
\widehat q\circ\mathsf{lift}_T
=
\mathsf{lift}_U\circ q.
$$
:::

:::{prf:proof}
Initiality gives the structural transformation.  Unit and bind compatibility
follow from the corresponding laws for $q$ and structural induction on free
requests.  Row labels are unchanged.
:::

:::{prf:theorem} Handler/morphism compatibility
:label: thm-generic-handler-morphism-v2

If return and operation clauses are mapped by $\widehat q$ to the target
handler clauses, then

$$
\widehat q\circ H^T_{\Delta,h}
=
H^U_{\Delta,\widehat qh}\circ\widehat q.
$$
:::

The proof is uniqueness of the handler fold, or structural induction on the
same return/matching/forwarding cases.

## 8. Lifting logical relations

Let $\mathcal R_T(X,Y)\subseteq TX\times UY$ be a base computation relation
compatible with:

- related returns;
- related bind continuations;
- the chosen base observations.

Assume parameter and response value relations for each operation signature.

Define the least structural resumption relation

$$
\widehat{\mathcal R}_\rho
\subseteq
\mathsf{Res}_{T,\rho}X
\times
\mathsf{Res}_{U,\rho}Y
$$

by relating one base layer through $\mathcal R_T$ and requiring corresponding
free requests to have the same nominal operation, related parameters, and
pointwise related response continuations.

:::{prf:theorem} Resumption logical-relation lifting
:label: thm-generic-resumption-relation-v2

Under the compatibility assumptions above,
$\widehat{\mathcal R}_\rho$ preserves return, bind, and row weakening.  If two
deep handlers have related return and operation clauses, they map related input
resumptions to related outputs.
:::

:::{prf:proof}
Induction/relator recursion over the exposed base layer and free request
structure.  Handler preservation has three cases: return uses related return
clauses, matching uses related operation clauses and the induction hypothesis
for resumptions, and forwarding preserves the nominal request while applying
the induction hypothesis pointwise.
:::

The equality graph of a monad morphism $q$ recovers
{prf:ref}`thm-generic-resumption-morphism-v2` and handler compatibility as a
special case.

## 9. Operational/denotational correspondence

Combine:

- a `BaseSafety` operational package;
- the resumption interpretation above;
- one-step soundness of every old base rule into $T$;
- reflection of the classified base outcomes by the chosen observation;
- semantic substitution.

:::{prf:theorem} Generic extension soundness
:label: thm-generic-extension-soundness-v2

Every extended operational step preserves resumption denotation, and direct
deep handling commutes with the generic handler fold.
:::

:::{prf:proof}
Old steps use base soundness.  New return and matching steps use the handler
fold equations and substitution.  Forwarded requests use the residual-request
equation.  Context closure uses resumption bind.
:::

:::{prf:theorem} Generic conditional adequacy
:label: thm-generic-extension-adequacy-v2

For a closed first-order computation whose deterministic execution reaches a
classified return, base outcome, or unhandled free request, the operational
observation agrees with the corresponding resumption observation, and
conversely.
:::

:::{prf:proof}
Iterate soundness and use generic extended decomposition.  Reflection of base
outcomes is delegated to the base observation hypothesis; free request
constructors are separated nominally.  The reverse implication uses the stated
termination assumption.
:::

Full adequacy without the termination premise additionally requires a
normalization theorem or a domain/coinductive model of divergence.

## 10. What the unordered theorem preserves

The complete conditional package is now:

- monad and row-refined sequencing;
- coherent subeffecting by row inclusion;
- user-defined free operations;
- exhaustive deep handlers;
- discharge of the handled interface;
- base denotation embedding;
- operational type safety and conservativity;
- monad-morphism lifting;
- logical-relation lifting;
- handler compatibility with morphisms and relations;
- one-step soundness;
- termination-conditional adequacy.

## 11. What it cannot preserve from the given data

No conclusion follows automatically about:

- the exact old base effect grade after handling;
- the number or order of clause invocations;
- validity of multi-shot duplication for linear resources;
- commutation with old base handlers;
- normalization;
- a resumption solution for every opaque monad.

These are not hidden proof obligations of the unordered theorem.  They require
additional information or restrictions and are separated into optional layers.
