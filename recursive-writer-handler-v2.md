# Recursive Writer handler v2

## Status

**Concrete least-fixed-point construction of the recursive deep handler.**
This replaces structural recursion on well-founded Writer trees.

## 1. Handler data

Handle interface $\Delta$ from input row $\rho\cup\{\Delta\}$ into target row
$\omega$, where $\Delta\notin\omega$.

Assume continuous denotations

$$
r:A\to\mathsf{CWTree}_\omega C
$$

and

$$
c_i:
P_i\to
(R_i\to\mathsf{CWTree}_\omega C)
\to
\mathsf{CWTree}_\omega C
$$

for every operation of $\Delta$.  The target typing prevents clauses and the
return clause from emitting an unhandled $\Delta$ directly.

## 2. Handler functional

Let

$$
\mathcal H
=
[\mathsf{CWTree}_{\rho\cup\{\Delta\}}A
\to_c
\mathsf{CWTree}_\omega C]
$$

be the pointed domain of continuous functions.  Define a continuous functional

$$
\Phi_h:\mathcal H\to\mathcal H
$$

by the following boundary equations.

Bottom:

$$
\Phi_h(g)(\bot)=\bot.
$$

Return:

$$
\Phi_h(g)(\mathsf{ret}_W(w,a))
=\mathsf{prefix}_w(r(a)).
$$

Matching request:

$$
\Phi_h(g)(\mathsf{req}_W(w;\Delta,i,p,k))
=
\mathsf{prefix}_w
\left(c_i(p,\lambda x.g(k(x)))\right).
$$

Residual request $\delta\neq\Delta$:

$$
\Phi_h(g)(\mathsf{req}_W(w;\delta,i,p,k))
=
\mathsf{req}_W(w;\delta,i,p,\lambda x.g(k(x))).
$$

The recursive deep handler is

$$
H_{\Delta,h}=\mathsf{lfp}(\Phi_h).
$$

## 3. Why least fixed point is needed

In the residual-request case, one output request guards the recursive call.  In
the matching case, the source request is eliminated and the clause may resume
immediately.  Therefore the recursive use of $g$ need not be guarded by an
output constructor.

For a source producing infinitely many matching requests and a clause that
simply resumes, the desired equation is schematically

$$
H(t)=H(t).
$$

Initiality is unavailable and naive productive corecursion rejects the
definition.  The least solution is bottom, matching an operational execution
that performs handler reductions forever without reaching an outward boundary.

## 4. Existence and equations

:::{prf:theorem} Recursive Writer handler existence
:label: thm-recursive-writer-handler-v2

If $r$ and all $c_i$ are continuous, then $\Phi_h$ is continuous,
$H_{\Delta,h}=\mathsf{lfp}(\Phi_h)$ exists, and it satisfies the four displayed
handler equations.
:::

:::{prf:proof}
Each branch is composed from continuous case analysis, `prefix`, the continuous
clause map, and pointwise application of $g$.  Hence $\Phi_h$ is continuous on
the function-space domain.  Kleene fixed-point iteration supplies its least
fixed point, and fixed-point unfolding gives the equations.
:::

The least solution is a semantic design choice justified by approximation from
finitely many operational unfoldings.  We do not claim that the raw equations
have only one mathematical solution.

## 5. Row discharge

:::{prf:theorem} Recursive Writer deep discharge
:label: thm-recursive-writer-discharge-v2

$H_{\Delta,h}$ maps into $\mathsf{CWTree}_\omega C$.  Since
$\Delta\notin\omega$, no finite outward observation of the result exposes a
$\Delta$ request.
:::

This includes divergent input and infinite handled behavior.  Such behavior may
map to bottom, but it cannot suddenly expose the eliminated nominal interface.

## 6. Compatibility with the finite fold

On an embedded well-founded input tree, induction on that tree shows that the
least-fixed-point handler agrees with the former structural handler fold.  Only
finitely many approximants of $H$ are needed to determine any finite input.

Thus adding recursion changes the construction principle but not the meaning of
handlers on recursion-free programs.

## 7. Bind compatibility

Assume the return and operation clauses have the usual algebraic compatibility
with target bind.  Then the recursive handler equations commute with sequencing.
The proof compares continuous maps on finite approximants and takes directed
suprema.

Without clause compatibility, $H$ remains a well-defined handler but need not be
a monad homomorphism.  This is the same distinction as in the finite model; the
presence of recursion makes continuity an additional premise.

## 8. Multi-shot clauses

A language-defined clause may invoke its resumption zero, one, or finitely many
times in one finite unfolding, and recursion may cause unbounded total use.
This does not invalidate continuity in an ordinary PCF/domain interpretation.

It does affect resource-sensitive base effects.  The Writer model is freely
duplicable, so the construction is valid here.  Generalization to linear IO,
regions, or one-shot continuations still needs the `HandlerInteraction`
capability identified by the unordered theorem.
