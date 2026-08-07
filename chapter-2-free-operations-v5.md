# Chapter II — ordered free-operation extension

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

- deterministic decomposition into return, base outcome, or exposed free
  request;
- substitution, preservation and effect-aware progress;
- old-syntax operational and observational conservativity;
- ordered upper-bound effect safety;
- the monad/graded sequencing laws of the finite tree extension;
- base morphisms and compatible logical relations by structural lifting;
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
