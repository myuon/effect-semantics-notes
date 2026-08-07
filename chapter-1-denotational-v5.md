# Chapter I — denotational semantics

## Status

**Semantic specification with concrete instances.**  This page interprets only
the fixed base calculus.

## 1. Generic graded interpretation

Let $\mathcal C$ be a bicartesian closed category and let

$$
(B,\cdot,1,\leq)
$$

be the ordered base-effect algebra.  A base denotational package supplies a
strong graded monad

$$
T_b:\mathcal C\to\mathcal C
$$

with

$$
\eta_A:A\to T_1A,
$$

$$
\mu_{b,c,A}:T_bT_cA\to T_{b\cdot c}A,
$$

strength

$$
\mathsf{st}_{b,X,A}:X\times T_bA\to T_b(X\times A),
$$

and coherent weakening

$$
\tau_{b,c,A}:T_bA\to T_cA
\qquad(b\leq c).
$$

Every base primitive has a denotation

$$
\beta^T:\llbracket P_\beta\rrbracket
\to T_{|\beta|}\llbracket R_\beta\rrbracket.
$$

It receives only its parameter.  The rest of the program is composed by graded
bind.

## 2. Interpretation of judgments

Types are interpreted by the bicartesian closed structure, with

$$
\llbracket A\xrightarrow{b}B\rrbracket
=
(T_b\llbracket B\rrbracket)^{\llbracket A\rrbracket}.
$$

Accordingly, application of
$M:(A\xrightarrow{e}B)!e_M$ to $N:A!e_N$ is interpreted by sequencing the
denotation of $M$, then that of $N$, then evaluation into $T_eB$.  Graded bind
therefore places the result in $T_{e_M\cdot e_N\cdot e}B$.

Judgments denote

$$
\llbracket\Gamma\vdash V:A\rrbracket:
\llbracket\Gamma\rrbracket\to\llbracket A\rrbracket,
$$

$$
\llbracket\Gamma\vdash M:A!b\rrbracket:
\llbracket\Gamma\rrbracket\to T_b\llbracket A\rrbracket.
$$

Return is interpreted by $\eta$.  Suppose

$$
m:\Gamma\to T_bA,
\qquad
n:\Gamma\times A\to T_cC.
$$

Then sequencing is

$$
\Gamma
\xrightarrow{\langle\mathsf{id},m\rangle}
\Gamma\times T_bA
\xrightarrow{\mathsf{st}}
T_b(\Gamma\times A)
\xrightarrow{T_bn}
T_bT_cC
\xrightarrow{\mu}
T_{b\cdot c}C.
$$

Conditionals and cases use coproduct elimination after both branches have been
weakened to their declared common upper bound.  Subeffecting is
interpreted by $\tau$.

## 3. Observation interface

To state adequacy, the package chooses observations

$$
\mathsf{observe}_{b,A}:T_bA\to\mathsf{Obs}_B(A).
$$

The observation is instance-specific and may itself carry branching structure.
Writer observes a value and log, State a value and final store, Exception a
value or error, and probabilistic choice a subdistribution of outcomes.  There
is no generic trace projection.  Effect safety and observational adequacy are
separate certificate fields.

## 4. Upper-bound Writer model

Work in $\mathbf{Set}$.  Let grades be message words with a compatible preorder
$\preceq$ that permits weakening.  Define

$$
T_bA=\{(w,a)\mid w\preceq b\}.
$$

Thus the denotation contains the actual Writer log, while $b$ merely bounds it.
The unit produces $(\epsilon,a)$ and graded bind concatenates the two contained
logs.  Monotonicity of $\preceq$ makes the result belong to $T_{b\cdot c}$.  The
primitive is

$$
\mathsf{tell}_a^T(*)=([a],*)\in T_{[a]}1.
$$

Weakening $b\preceq c$ retains the same pair and changes only its static
membership proof.  Observation forgets that proof:

$$
\mathsf{observe}_{b,A}(w,a)=(w,a).
$$

If a coarser Writer effect system remembers only whether writing may occur,
use the corresponding coarser preorder and carrier.  Exactness is not required
by the generic calculus.

## 5. State model

Let $S$ be the store.  The ordinary State carrier can be used at every grade:

$$
T_bA=S\to A\times S.
$$

The grade is a static index; it need not be reconstructed from an element of
the carrier.  Return is

$$
\eta(a)(s)=(a,s),
$$

and bind is

$$
(m\mathbin{\gg=} f)(s)=
\text{let }(a,s_1)=m(s)
\text{ in }f(a)(s_1).
$$

The primitives are

$$
\mathsf{get}^T(*)(s)
=(s,s),
$$

$$
\mathsf{put}^T(s') (s)
=(*,s').
$$

Choose primitive grades $\mathsf{read}$ and $\mathsf{write}$ and type sequencing
with their noncommutative product.  The denotation validates state behavior;
the typing derivation validates the upper-bound effect order.

## 6. Exception model

At every grade use the ordinary exception carrier

$$
T_bA=A+\mathsf{Err}.
$$

Bind short-circuits in the error case:

$$
(\mathsf{inr}\,e)\mathbin{\gg=} f
=\mathsf{inr}\,e,
$$

$$
(\mathsf{inl}\,a)\mathbin{\gg=} f=f(a).
$$

The primitive raise is

$$
\mathsf{raise}_e^T(*)
=\mathsf{inr}\,e.
$$

The static effect system may still conservatively assign
$\mathsf{raise}\cdot b$ to `raise; M`; the denotation does not claim that $M$
runs.  A more precise abortive grade algebra may collapse this product, but the
generic semantics does not require it.

## 7. Probabilistic model

For finite probabilistic choice, take

$$
T_bA=\mathsf{SubDist}(A)
$$

at every grade.  Return is Dirac mass and bind is Kleisli integration:

$$
\eta(a)=\delta_a,
\qquad
(\mu\mathbin{\gg=}f)(b)=
\sum_{a}\mu(a)f(a)(b).
$$

Weakening is the identity on the underlying subdistribution.  Interpret fair
random choice by

$$
\mathsf{randomBool}^T(*)
=\tfrac12\delta_{\mathsf{true}}
 +\tfrac12\delta_{\mathsf{false}}.
$$

For a closed ground computation, observation is its resulting
subdistribution.  Probabilistic adequacy is the equality

$$
\Pr[M\Downarrow v]
=\llbracket M\rrbracket(v).
$$

When all recursion-free primitive kernels have total mass one, the result is a
probability distribution.  With abortive divergence it remains a
subdistribution.

## 8. Model boundary

Writer can reflect its upper bound directly in the carrier, while State and
Exception can use phantom grade indices.  Therefore the generic theorem must
not require a denotation to reveal which effects occurred.  It requires only a
coherent strong graded interpretation and a separately stated adequacy theorem.
The generic interface does not require the operational response monad
$\mathcal K$ to be `Id`; it requires the selected denotational observation to
agree with the $\mathcal K$-structured operational outcome.
