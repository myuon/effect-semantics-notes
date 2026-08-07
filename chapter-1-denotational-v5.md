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
\llbracket A\to(B!b)\rrbracket
=
(T_b\llbracket B\rrbracket)^{\llbracket A\rrbracket}.
$$

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
placed at their declared common trace-language bound.  Subeffecting is
interpreted by $\tau$.

## 3. Trace observation interface

The categorical denotation need not literally be a trace.  To state ordered
effect soundness and adequacy, the package additionally chooses observations

$$
\mathsf{observe}_{b,A}:T_bA\to\mathsf{Obs}_B(A)
$$

and a behavior projection

$$
\mathsf{beh}:\mathsf{Obs}_B(A)\to\mathsf{Trace}_B\times\mathsf{Exit}_B.
$$

They must respect unit, completion-sensitive sequencing and weakening.  In
particular, observed sequencing concatenates the second ordered contribution
only when the first computation returns normally.

## 4. Exact Writer model

Work in $\mathbf{Set}$ with grades $w\in\mathsf{Msg}^*$.  Define

$$
T_wA=A.
$$

The grade already records the exact log, so the carrier need not store it
again.  Unit and multiplication are identities at the appropriately indexed
types, and

$$
\mathsf{tell}_a^T(*)=*\in T_{[a]}1.
$$

The observation restores the index:

$$
\mathsf{observe}_{w,A}(a)=((w,\checkmark),a).
$$

For a more conventional upper-bound presentation one may instead use the
coarser two-grade Writer model $T_1A=A$ and
$T_\mathsf{write}A=\mathsf{Msg}^*\times A$.  The exact-word model is preferable
on the ordered main line; the coarse model remains its abstraction.

## 5. State-and-trace model

Let $S$ be the store and $\mathsf{Tr}_S$ the concrete state-event words.  For a
trace language $L$, define

$$
T_LA=
\{f:S\to A\times S\times\mathsf{Tr}_S
\mid
\forall s.\ \pi_3(f(s))\in L\}.
$$

If static grades abstract concrete values, replace membership by membership in
the concretization $\gamma(L)$.  Return is

$$
\eta(a)(s)=(a,s,\epsilon),
$$

and bind is

$$
(m\mathbin{\gg=} f)(s)=
\text{let }(a,s_1,t_1)=m(s),
(c,s_2,t_2)=f(a)(s_1)
\text{ in }(c,s_2,t_1\cdot t_2).
$$

The primitives are

$$
\mathsf{get}^T(*)(s)
=(s,s,[\mathsf{get}(s)]),
$$

$$
\mathsf{put}^T(s') (s)
=(*,s',[\mathsf{put}(s')]).
$$

This model records both state threading and event order.  Projecting away the
third component recovers the ordinary State monad.

## 6. Exception-and-trace model

Let $\mathsf{Beh}_X=\mathsf{Tr}_X\times
(\{\checkmark\}+\mathsf{Err})$.  Let

$$
T_LA=
\{(t,o)\mid
o=\mathsf{inl}\,a\Rightarrow(t,\checkmark)\in L,
\quad
o=\mathsf{inr}\,e\Rightarrow(t,\mathsf{abort}(e))\in L\},
$$

where $L\subseteq\mathsf{Beh}_X$.  Bind appends the second trace only in the
return case:

$$
(t,\mathsf{inr}\,e)\mathbin{\gg=} f
=(t,\mathsf{inr}\,e),
$$

$$
(t,\mathsf{inl}\,a)\mathbin{\gg=} f
=
\text{let }(u,o)=f(a)\text{ in }(t\cdot u,o).
$$

The primitive raise is

$$
\mathsf{raise}_e^T(*)
=([\mathsf{raise}(e)],\mathsf{inr}\,e).
$$

The short-circuiting bind explains denotationally why effects after an
exception do not occur.  Its result is indexed by the completion-sensitive
language product $L\mathbin{;}K$, which contains the unchanged abort behavior
from $L$.

## 7. Model boundary

The exact Writer construction uses grades as data, while State and Exception
use carriers that retain runtime-dependent observations.  The generic theorem
must therefore quantify over an observation-compatible graded model rather
than require every base effect to have the same representation.
