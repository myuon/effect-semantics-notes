# Random/SubDist end-to-end package instance

:::{admonition} Formalization status — Random
:class: warning
**Boundary / paper instance.** The generic framework permits nondeterministic base behavior only after choosing an observation domain and adequacy notion. Unlike Writer, State, and Exception, this page does not currently have a complete recursive Lean instance. Do not infer determinism or adequacy from `BasePackage` notation alone.
:::

## Status

**Concrete finite probabilistic derivation.**  This page checks that the main
theorem is not secretly deterministic.  All response distributions are
finitely supported and all source programs are recursion-free.

## 1. Base package

Let the base primitive be

$$
\mathsf{randomBool}:1\to\mathsf{Bool}
$$

with grade $\mathsf{rnd}$.  Take

$$
\mathcal K=T=\mathsf{FinSubDist},
$$

the finite subdistribution monad, and

$$
\mathsf{resp}_{\mathsf{randomBool}}(*)
=\tfrac12\delta_{\mathsf{true}}
+\tfrac12\delta_{\mathsf{false}}.
$$

The effect grade is a static upper bound; the carrier may be used with a
phantom grade and coherent weakening.  Operational composition multiplies
branch weights and sums weights at equal outcomes.  Denotational Kleisli bind
does exactly the same.

For every recursion-free ground $M$,

$$
\Pr[M\Downarrow o]
=\llbracket M\rrbracket(o).
$$

Induction on the finite response tree establishes `BasePackage`.  Unique
evaluation position remains true; only the selected primitive response
branches.

## 2. Free operation and canonical observation

Add $\mathsf{ask}:1\to\mathsf{Bool}$ in interface $\Delta$.  The indexed layer
is the construction of the previous page with outer
$\mathsf{FinSubDist}_b$.  Finite support, finite response type and finite source
trees give the required indexed initial algebra.  Its base action samples a
finite distribution of residual trees and flattens it by finite
subdistribution bind:

$$
\mathsf{baseAct}_{b,d}:
\mathsf{FinSubDist}(\mathsf F_dA)
\to\mathsf F_{b\cdot d}A.
$$

The finite-sum monad laws supply the required coherence.

The extended observation is

$$
\mathsf{Obs}^\Delta(A)
\cong
\mathsf{FinSubDist}\left(
A+\mathsf{Out}_B+
1\times(\mathsf{Bool}\to\mathsf{Obs}^\Delta(A))
\right).
$$

It retains probability weights around returns and exposed `ask` nodes.

## 3. Program calculation

Consider

```text
let c <- randomBool(*) in
if c then ask(*) else return false
```

with upper bound

$$
\mathsf{rnd}\cdot\Delta.
$$

The operational observation is

$$
\tfrac12\delta_{\mathsf{askObs}(*,\lambda r.\mathsf{returnObs}(r))}
+\tfrac12\delta_{\mathsf{returnObs}(\mathsf{false})}.
\tag{Random-Free-Obs}
$$

The first half selects `true` and exposes `ask`; the second selects `false`
and returns without issuing the optional effect.  The indexed denotational
fold gives the same subdistribution.

## 4. Probabilistic TT pole

Define

$$
C\mathrel{\mathcal O^{\mathsf{rnd}}_e}t
\quad\Longleftrightarrow\quad
\forall o.\ 
\mathsf{run}(C)(o)=\mathsf{observe}(t)(o).
$$

Pole closure under probabilistic bind follows from the finite sum calculation

$$
\sum_x\mu(x)k_x(o)
=
\sum_y\nu(y)\ell_y(o)
$$

because the operational and denotational sides use the same finite outcome
set, $\mu=\nu$ pointwise, and corresponding continuations have equal outcome
weights.  A genuinely heterogeneous probabilistic relation would instead
need a coupling/relator premise.  Free-node closure is pointwise on the two Boolean responses.
Weakening is again observationally inert.

Thus the graded `TTClosure` laws hold.  In particular, the fundamental lemma
concludes equality of complete subdistributions, not merely equality of their
supports or expected return values.

## 5. Shallow handling

Handle `ask` with

```text
return x  -> return x
ask(_, k) -> k true
```

The affine response is pure.  The effect bound changes by

$$
\mathsf{rnd}\cdot\Delta
\longmapsto
\mathsf{rnd}.
$$

Applying the structural shallow map to `(Random-Free-Obs)` produces

$$
\tfrac12\delta_{\mathsf{true}}
+\tfrac12\delta_{\mathsf{false}}.
$$

Operational reduction produces the same distribution.  `TTClause` holds
because related continuations are applied to the same Boolean response
`true`; linearity of finite subdistribution bind handles the outer random
choice.

## 6. What this instance proves—and does not prove

The instance validates:

- response branching without reduction nondeterminism at the evaluation
  position level;
- free extension of a probabilistic base;
- canonical probabilistic pole closure;
- graded TT fundamental lemma;
- shallow-handler adequacy as equality of subdistributions.

It does not cover countably supported distributions, continuous sampling or
measurable kernels.  Those require a different carrier category and the
codensity-lifting/measurability hypotheses are not supplied by the finite
theorem.
