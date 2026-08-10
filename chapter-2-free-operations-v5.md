# Chapter II — ordered free-operation extension

:::{admonition} Formalization status
:class: tip
The typed finite carrier, monad laws, base embedding, morphisms, relations, TT lifting, and finite adequacy are **Lean checked**; see the [Chapter-II table](review-guide.md#chapter-ii-free-operations). The general paper theorem assumes the strong graded FreeT objects described in [FreeT existence](graded-freet-existence-v1.md). The stronger grade-indexed carrier notation in this chapter is a **Paper abstraction** layered over the separately mechanized ordered effect-language bounds.
:::

## Status

**Working extension specification.**  This chapter adds user-defined
operations but no handlers and no recursion.

## 1. Interfaces and terms

Let $\mathcal D$ be a set of nominal interfaces.  Each interface has a typed
signature

$$
\Sigma(\Delta)=
\{\mathsf{op}_{\Delta,i}:P_i\to R_i\}_{i\in I_\Delta}.
$$

Source operations are ordinary computations of their response type:

$$
\frac{\Gamma\vdash V:P_i}
     {\Gamma\vdash\mathsf{op}_{\Delta,i}(V):R_i!\Delta}.
$$

There is no continuation in this syntax.  When an operation becomes exposed,
its continuation is the surrounding CBV evaluation context.

## 2. Extended ordered effects

The extended effect monoid is the free product

$$
\widehat E=B*\mathcal D^*.
$$

Its reduced expressions alternate between non-unit base segments and free
interface symbols.  They are static bounds, not runtime traces.  No exchange
law is assumed:

$$
b\cdot\Delta\neq\Delta\cdot b.
$$

Equip $\widehat E$ with the least compatible preorder extending the base
preorder and the adopted optionality laws

$$
1\leq\Delta
\qquad(\Delta\in\mathcal D).
$$

Consequently $b\cdot e\leq b\cdot\Delta\cdot e$: a computation that does not
perform $\Delta$ may be given a bound that says $\Delta$ might occur there.
Conditionals are typed by weakening both branches to a chosen common upper
bound.  No effect-level sum or trace-language union is added to the core.

## 3. Operational exposure

Evaluation follows the base CBV rules until it reaches

$$
E[\mathsf{op}_{\Delta,i}(V)].
$$

Without a handler this is a suspended free request with parameter $V$ and
metatheoretic continuation

$$
k=\lambda r.E[\mathsf{return}\,r].
$$

The syntax did not pass $k$ to the operation; the machine reconstructs it from
the evaluation context.

## 4. Finite operation trees

For recursion-free proofs, use well-founded trees

$$
\begin{aligned}
t::={}&\mathsf{ret}(a)\\
&\mid\mathsf{base}_\beta(p,r\mapsto t_r)\\
&\mid\mathsf{free}_{\Delta,i}(p,r\mapsto t_r).
\end{aligned}
$$

Return and substitution give the tree family its free-monad structure.  The
tree records algebraic operation/continuation structure for denotational
purposes; it is not the static effect annotation.  A fold maps base nodes into
the selected base semantics while leaving free nodes visible.

## 5. First extension theorem target

For every recursion-free base package satisfying Chapter I, adding $\Sigma$
should preserve:

- unique evaluation-position decomposition into return, an internal redex,
  a base request, or an exposed free request; primitive responses may still
  branch through $\mathcal K$;
- substitution, preservation and effect-aware progress;
- old-syntax operational and observational conservativity;
- ordered upper-bound effect safety;
- the monad/graded sequencing laws of the finite tree extension;
- base morphisms by functorial lifting, compatible graded relators by the least
  structural lifting, and observational relations by graded TT-lifting;
- adequacy after choosing an observation for unhandled requests.

The last item is conditional: a base observation that cannot represent a free
request must be extended rather than silently reused.

## 6. Concrete checkpoints

The theorem will first be calculated for:

- **Writer:** possible writes occur before or after free requests as reflected
  by the noncommutative bound;
- **State:** ordered reads/writes determine which parameters reach later
  requests;
- **Exception:** an earlier base exception can prevent a later free request
  from being exposed.

These examples test that the static order constrains possible execution while
remaining an upper approximation.

The full Chapter-II cycle is developed in:

- [Direct semantics and concrete programs](chapter-2-operational-examples-v5.md);
- [Denotational free extension](chapter-2-denotational-v5.md);
- [Preservation proofs and `FreeCert`](chapter-2-certificate-v5.md).
