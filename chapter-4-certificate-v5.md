# Chapter IV — recursion certificate and derived-deep theorem

## Status

**Conditional paper theorem.**  This page records exactly what must be added
to `ShallowCert` and what is then preserved.

## 1. Recursive input certificate

For a recursive extension $L^{\mathsf{rec}}$ and recursive carrier $\mathsf R$,
define

$$
\begin{aligned}
\mathsf{RecBaseCert}(L^{\mathsf{rec}},\mathsf R,K):=\{\;&
\mathsf{unfoldTy},\mathsf{unfoldPres},
\bot,(\bigsqcup),\mathsf{cont},\mathsf{iter},\\
&\mathsf{fixAgree},\mathsf{admRel},\mathsf{resIso},
\mathsf{obsLevel},K,\mathsf{closureLaw}\;\}.
\end{aligned}
\tag{RecBaseCert}
$$

The syntactic and order-theoretic fields are

$$
\begin{aligned}
\mathsf{unfoldTy}:&\quad
\Gamma,f:A\xrightarrow{e}B,x:A\vdash M:B!e,\\
\mathsf{unfoldPres}:&\quad
\Gamma\vdash\mathsf{call}(\mathsf{rec}\ f(x).M,V):B!e
\Rightarrow\Gamma\vdash M[f_{\mathsf{rec}}/f,V/x]:B!e,\\
&\forall A.\ (\mathsf R A,\sqsubseteq,\bot)
\text{ is a pointed $\omega$-cpo},\\
\mathsf{iter}(F):&\quad
\operatorname{lfp}(F)=\bigsqcup_{n<\omega}F^n(\bot)
\quad(F\text{ continuous}),\\
\mathsf{fixAgree}:&\quad
\llbracket\mathsf{fix}\ f.M\rrbracket
=\operatorname{lfp}(\lambda f.\llbracket M\rrbracket),\\
\mathsf{admRel}:&\quad
(x_n\mathrel R y_n)_{n<\omega}\Rightarrow
\bigsqcup_nx_n\mathrel R\bigsqcup_ny_n.
\end{aligned}
$$

The resumption and ordered-closure fields are

$$
\mathsf{resIso}_{A}:\quad
\mathsf R A\cong T(A+\Sigma(\mathsf R A)),
$$

$$
K:\widehat E\to\widehat E,qquad
1\leq K(e),qquad e\cdot K(e)\leq K(e),qquad
e\leq f\Rightarrow K(e)\leq K(f).
\tag{Closure}
$$

`cont` states that return, bind, base/free constructors and the Chapter-III
shallow map preserve suprema of $\omega$-chains.  `obsLevel` explicitly selects
finite-boundary, bottom/divergence, or productive-infinite observation and
supplies the corresponding reflection map.

Items 2–5 are genuine additional hypotheses.  They cannot be reconstructed
from the finite `ShallowCert` or from monad laws.

## 2. Recursive safety

:::{prf:theorem} Recursive preservation and progress
:label: thm-recursive-preservation-v5

If

$$
\mathsf{ShallowCert}(\Delta,h,\Phi_h)
\land\mathsf{RecBaseCert}(L^{\mathsf{rec}},\mathsf R,K),
$$

then

$$
\begin{aligned}
&\Gamma\vdash M:A!e\land M\to M'
 \Rightarrow\Gamma\vdash M':A!e,\\
&\vdash M:A!e\Rightarrow
 \mathsf{Boundary}(M)\mathbin{\dot\vee}\mathsf{UniquePos}(M),\\
&M'\in\operatorname{supp}(\mathsf{step}(M))
 \Rightarrow\vdash M':A!e.
\end{aligned}
$$

Consequently, every maximal supported branch reaches a classified boundary or
is infinite.
:::

The final alternative is new: normalization from the recursion-free chapters
does not survive.

## 3. Derived/deep coincidence

:::{prf:theorem} Derived source handler equals semantic deep handler
:label: thm-derived-deep-coincidence-v5

If $\mathcal D_h$ is continuous and `fixAgree` holds, then

$$
\llbracket\mathsf{deep}_{\Delta,h}^{\mathsf{derived}}(M)\rrbracket
=\operatorname{lfp}(\mathcal D_h)(\llbracket M\rrbracket),
\qquad
\operatorname{lfp}(\mathcal D_h)=
\bigsqcup_n\mathcal D_h^n(\bot).
$$
:::

**Proof.**  Unfolding the source `loop` once gives exactly the Chapter-III
shallow map whose matching continuations are wrapped by the previous
approximation; nonmatching continuations remain under that shallow map.  Hence
the $n$th source approximant denotes
$\mathcal D_h^n(\bot)$.  Continuity and the source-fixpoint agreement field
identify their suprema. $\square$

## 4. Deep elimination

:::{prf:theorem} Elimination of an exhaustive interface
:label: thm-deep-elimination-v5

If

$$
\mathsf{Exhaustive}_\Delta(h)
\land\mathsf{ClauseFree}_\Delta(h)
\land\mathsf{WrappedMatch}(h)
\land\mathsf{TransparentForward}(h),
$$

then

$$
\forall n,C.\quad
\mathsf{deep}^{\mathsf{derived}}_{\Delta,h}(M)\to^n C
\Rightarrow\neg\mathsf{EscapingReq}_\Delta(C).
\tag{Deep-Elim}
$$
:::

**Proof sketch.**  Induct on finite unfoldings and finite reductions.  A
matching request enters a clause; a nonmatching request is rebuilt with the
invariant in its continuation.  Admissibility closes the semantic statement
at the least fixed point.  Divergence does not invalidate the prefix safety
invariant.

## 5. Adequacy

:::{prf:theorem} Recursive adequacy transport
:label: thm-recursive-adequacy-v5

If

$$
\mathsf{Admissible}(R)
\land\mathsf{Compat}_{\mathsf{iter}}(R)
\land\mathsf{Compat}_{h}(R)
\land\mathsf{Reflect}_{\ell}(R,\mathsf{obs}),
$$

then, for every closed ground $M$,

$$
M\Downarrow_{\ell}o
\Longleftrightarrow
\mathsf{observe}_{\ell}(\llbracket M\rrbracket)=o.
$$

Here $\ell$ is exactly the observation level stored in `RecBaseCert`; no
stronger divergence or productive-infinite conclusion is implicit.
:::

The recursion case uses fixed-point induction.  The handler case uses the
derived/deep coincidence theorem rather than assuming a primitive deep
operator.

## 6. Ordered-effect theorem

For each finite unfolding, Chapter III transforms occurrences in their
original order, taking the prefix before each first match to be $\Delta$-free.
For unbounded recursion, suppose $e^*$ safely closes finite
iteration and $\Phi_h$ is continuous/closure-compatible.  Then the transformed
recursive bound is safely covered by the corresponding closed output, for
example

$$
(b\cdot\Delta\cdot e)^*
\longmapsto
(b\cdot e'\cdot e)^*.
$$

This is an inequality-level may-effect result.  Exact equality, multiplicity,
or a least principal word is outside the basic theorem.

## 7. Chapter-IV structure-preservation theorem

### Formal definition of `DeepCert`

Define

$$
\begin{aligned}
\mathsf{DeepCert}(\Delta,h,\Phi_h,K):=\{\;&
\mathsf{recPres},\mathsf{recProgress},\mathsf{oldCons},
\mathsf{defDeep},\\
&\mathsf{deepEq}_{\mathsf{ret}},\mathsf{deepEq}_{\mathsf{match}},
\mathsf{deepEq}_{\mathsf{forward}},\\
&\mathsf{eliminate}_\Delta,\mathsf{adequate}_{\ell},
\mathsf{iterEffect}\;\}.
\end{aligned}
\tag{DeepCert}
$$

Besides the equations above, its characteristic fields are

$$
\begin{aligned}
\mathsf{defDeep}:&\quad
\mathsf{deep}^{\mathsf{derived}}_{\Delta,h}
=\operatorname{lfp}(\mathcal D_h),\\
\mathsf{eliminate}_\Delta:&\quad
\forall n,C.\quad\mathsf{deep}^{\mathsf{derived}}_{\Delta,h}(M)\to^nC
\Rightarrow\neg\mathsf{EscapingReq}_\Delta(C),\\
\mathsf{iterEffect}:&\quad
\Phi_h((b\cdot\Delta\cdot e)^*)
\leq(b\cdot e'\cdot e)^*,
\quad e^*:=K(e).
\end{aligned}
$$

:::{prf:theorem} Recursive derived-deep certificate
:label: thm-recursive-derived-deep-certificate-v5

The complete implication is

$$
\begin{aligned}
&\mathsf{ShallowCert}(\Delta,h,\Phi_h)
\land\mathsf{RecBaseCert}(L^{\mathsf{rec}},\mathsf R,K)\\
&\land\mathsf{HandlerCert}(\Delta,h,\Phi_h)
\land\mathsf{Exhaustive}_\Delta(h)
\land\mathsf{ClauseFree}_\Delta(h)\\
&\land\mathsf{Continuous}(\mathcal D_h)
\land\mathsf{ClosureCompat}(K,\Phi_h)
\land\mathsf{Reflect}_{\ell}(R,\mathsf{obs})\\
&\quad\Longrightarrow
\mathsf{DeepCert}(\Delta,h,\Phi_h,K).
\end{aligned}
\tag{Deep-Transport}
$$
:::

## 8. Sharp limits

The fixed-point induction, elimination invariant and recursive logical-relation
argument are expanded in
[Chapter IV — detailed recursive and derived-deep proofs](chapter-4-proof-details-v5.md).

The theorem does not provide termination, exact effect counts, unrestricted
multi-shot resource safety, commutation with old handlers, full abstraction,
or productive traces in a bottom-only model.  These require separate
certificates rather than stronger prose around “an arbitrary base effect.”
