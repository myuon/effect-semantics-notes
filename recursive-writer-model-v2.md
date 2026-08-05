# Recursive Writer model v2

## Status

**Concrete construction of the recursive unordered extension.**  This is the
first test of the complete-Elgot/domain-theoretic proposal.  It observes finite
Writer prefixes and divergence, but deliberately does not retain an infinite
stream of `tell` actions.

## 1. Operational boundary observations

Fix a Writer monoid $(W,\epsilon,\cdot)$.  Run a closed computation until the
first external boundary:

1. return after a finite log $w$;
2. expose a free request after a finite log $w$;
3. continue forever without reaching either boundary.

Write these observations as

$$
\mathsf{ret}(w,a),
\qquad
\mathsf{req}(w;\Delta,i,p,k),
\qquad
\bot.
$$

The third case includes both a silent recursive loop and an execution that
performs infinitely many `tell` steps before reaching no boundary.  This is a
chosen coarse observation, not a claim that those executions are contextually
equivalent in every language.

## 2. Domain equation

For a row $\rho$, define the pointed recursive domain

$$
\mathsf{CWTree}_\rho A
\cong
\left(
W\times
\left(
A+
\sum_{\Delta\in\rho}
\sum_{i\in I_\Delta}
P_i\times(R_i\to\mathsf{CWTree}_\rho A)
\right)
\right)_\bot.
$$

The constructors are:

$$
\bot,
$$

$$
\mathsf{ret}_W(w,a),
$$

$$
\mathsf{req}_W(w;\Delta,i,p,k).
$$

Assume the ordinary pointed-domain interpretation:

- $W$, parameters, responses, and ground values are flat domains;
- function spaces contain continuous functions with pointwise order;
- sums and products are the corresponding domain constructors;
- the recursive equation is solved in a standard category of domains and
  continuous maps.

This is the Writer instance of

$$
\nu X.\,T_\bot(A+\Sigma_\rho X),
\qquad
T_\bot X=(W\times X)_\bot.
$$

The order is approximation: $\bot$ contains no finite boundary information,
and request continuations are ordered pointwise.

## 3. Prefix action

Define the continuous action

$$
\mathsf{prefix}_u:\mathsf{CWTree}_\rho A
\to\mathsf{CWTree}_\rho A
$$

by

$$
\mathsf{prefix}_u(\bot)=\bot,
$$

$$
\mathsf{prefix}_u(\mathsf{ret}_W(w,a))
=\mathsf{ret}_W(u\cdot w,a),
$$

$$
\mathsf{prefix}_u(\mathsf{req}_W(w;\delta,i,p,k))
=\mathsf{req}_W(u\cdot w;\delta,i,p,k).
$$

In particular, `tell u; loop` denotes $\bot$, not an infinite log beginning in
$u$.  That is exactly the observation choice made above.

The laws

$$
\mathsf{prefix}_\epsilon=\mathsf{id},
\qquad
\mathsf{prefix}_u\circ\mathsf{prefix}_w
=\mathsf{prefix}_{u\cdot w}
$$

hold, including at bottom.

## 4. Monad structure

Return is

$$
\eta(a)=\mathsf{ret}_W(\epsilon,a).
$$

Bind is the least continuous solution of

$$
\bot\mathbin{\gg=}f=\bot,
$$

$$
\mathsf{ret}_W(w,a)\mathbin{\gg=}f
=\mathsf{prefix}_w(f(a)),
$$

$$
\mathsf{req}_W(w;\delta,i,p,k)\mathbin{\gg=}f
=
\mathsf{req}_W
(w;\delta,i,p,\lambda r.k(r)\mathbin{\gg=}f).
$$

:::{prf:theorem} Recursive Writer row monad
:label: thm-recursive-writer-monad-v2

$\mathsf{CWTree}$ is a pointed locally continuous monad.  Restricting request
labels gives

$$
\eta:A\to\mathsf{CWTree}_\varnothing A,
$$

$$
\mathsf{CWTree}_\rho A\times
(A\to\mathsf{CWTree}_\sigma C)
\to
\mathsf{CWTree}_{\rho\cup\sigma}C,
$$

with continuous weakening by row inclusion.
:::

:::{prf:proof}
The equations define continuous maps by the recursive-domain solution.  The
monad laws are equalities between continuous maps.  They hold on every finite
compact approximation by the same return/request calculation as the
well-founded Writer tree, and hence on their directed suprema.  Bottom is
strict for bind.  Row labels are preserved structurally and combined by union.
:::

## 5. Interpreting recursion

For a continuous functional

$$
F:D\to D,
$$

interpret recursion by the least fixed point

$$
\mathsf{lfp}(F)
=
\bigsqcup_{n<\omega}F^n(\bot).
$$

The operational unfolding equation becomes the semantic fixed-point equation

$$
\mathsf{lfp}(F)=F(\mathsf{lfp}(F)).
$$

Thus the new recursive application step is sound by construction.

For example,

$$
\llbracket\mathsf{rec}\ f(u).f(u)\rrbracket=\bot.
$$

## 6. Relation to the finite Writer tree

Every well-founded tree embeds as a nonbottom element of $\mathsf{CWTree}$.
With infinite response types the whole embedded continuation need not be a
compact element; only each finite observation/projection is required to be
finitely witnessed.  The embedding preserves:

- return;
- prefix;
- bind;
- request labels and continuations;
- row weakening.

Therefore the recursive model is conservative over the former denotation on
recursion-free programs, provided the interpretations of old primitives are
the embedded ones.

## 7. What remains observable

At row $\varnothing$ the equation reduces to

$$
\mathsf{CWTree}_\varnothing A
\cong(W\times A)_\bot.
$$

Hence a fully handled closed program has exactly one of:

- a terminating Writer result $(w,a)$;
- bottom.

This makes the empty-row Writer instance the simplest place to prove
termination/divergence adequacy.
