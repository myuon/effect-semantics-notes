# Chapter IV — recursive denotation and the derived handler

## Status

**Conditional semantic construction.**  The base model must provide a chosen
recursion principle; graded-monad laws alone are insufficient.

## 1. Recursive carrier

Replace the finite free carrier by a selected solution

$$
\mathsf R_\Sigma(T)A
\cong T\bigl(A+\Sigma(\mathsf R_\Sigma(T)A)\bigr).
\tag{R}
$$

One sufficient setting is a pointed $\omega$-cpo category in which $T$ and
$\Sigma$ are locally continuous and (R) has a minimal solution.  A complete
Elgot or guarded account is also admissible, but its chosen iteration must be
related separately to source unfolding.

## 2. Fixpoint

If a recursive definition denotes a continuous functional

$$
F:(A\to\mathsf R B)\to(A\to\mathsf R B),
$$

interpret it by

$$
\operatorname{lfp}(F)=\bigsqcup_{n<\omega}F^n(\bot).
$$

The finite approximants are precisely the computations obtained by allowing
at most $n$ recursive unfoldings.  This supplies the bridge used later in the
adequacy proof.

## 3. Semantic shallow handler

Chapter III provides the first-boundary map

$$
\mathsf{sh}_{\Delta,h}:\mathsf R A\to\mathsf R C,
$$

whose matching and forwarding equations do not recursively handle their
continuations.

## 4. Semantic functional for deep handling

For a candidate map $g:\mathsf R A\to\mathsf R C$, form a shallow handler
$h[g]$ whose continuations are wrapped by $g$:

$$
h[g]_i(p,k)=h_i(p,\lambda r.g(k(r))),
$$

and whose forwarding continuation is likewise $\lambda r.g(k(r))$.  Define

$$
\mathcal D_h(g)=\mathsf{sh}_{\Delta,h[g]}.
$$

Then the denotation of the derived source program is

$$
\mathsf{deep}_{\Delta,h}=\operatorname{lfp}(\mathcal D_h).
$$

Consequently it satisfies the familiar deep equations, but those equations
are consequences of shallow handling plus the selected fixpoint—not a second
primitive semantic operation.

## 5. Ordered effects under iteration

Let $K$ be a closure operation on ordered effects satisfying

$$
1\le K(e),\qquad e\cdot K(e)\le K(e),
$$

and monotonicity.  Write $e^*=K(e)$.  It is a safe upper bound for any finite
number of recursive unfoldings.  Noncommutativity is retained: in general
$e^*d\ne de^*$.

For a deep affine handler, finite approximants replace matching $\Delta$
symbols in order.  Passing to the supremum requires the handler transformer
$\Phi_h$ to be compatible with the selected closure/limits.  A typical safe
statement is

$$
\Phi_h\bigl((b\cdot\Delta\cdot e)^*\bigr)
\le (b\cdot e'\cdot e)^*.
$$

Equality is not claimed without a free or principal effect algebra.

## 6. Interface elimination

Assume the handler is exhaustive for $\Delta$, its clauses and return branch
are outwardly $\Delta$-free, and forwarding recursively preserves the pending
handler.  Every finite approximant of $\mathsf{deep}_{\Delta,h}(M)$ is then
$\Delta$-free at its outer boundary.  Admissibility/continuity lifts this
safety property to the least fixed point.

The resulting program may denote $\bot$, an old base outcome, or an infinite
old-effect behavior.  Interface elimination is therefore a safety theorem,
not normalization.

## 7. Observation levels

- **Finite boundary:** returns, old outcomes, and escaping free requests.
- **Divergence:** reflection of $\bot$ or infinite reduction.
- **Productive infinity:** infinite Writer/State traces.

The first follows from the recursive logical relation below; the second and
third require corresponding fields in the base adequacy package.  A theorem
must not silently upgrade one level into another.
