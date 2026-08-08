# Chapter III — shallow-handler proofs and `ShallowCert`

## Status

**Conditional paper theorem.**  The affine fragment has a derived effect
transformer.  The general fragment is conditional on a supplied handler-effect
certificate.

## 1. Typing preservation

### Lemma III.1 — continuation typing

If

$$
\mathcal E[\mathsf{op}_{\Delta,i}(V)]:A!e_{\mathsf{in}},
$$

then residual-context typing gives an effect $e_k$ such that

$$
k=\lambda r.\mathcal E[\mathsf{return}\,r]
:
R_i\xrightarrow{e_k}A.
$$

The ordered input bound contains the primitive grade $\Delta$ before $e_k$,
up to the declared weakening.

### Theorem III.2 — handler preservation

If

$$
\mathsf{FreeCert}(L_B+\Sigma,\widehat E,\mathcal K,\mathsf F_\Sigma(T))
\land\mathsf{HandlerCert}(\Delta,h,\Phi_h)
\land\Gamma\vdash M:A!e,
$$

then

$$
\Gamma\vdash
\mathsf{shallow}_\Delta M\ \mathsf{with}\ h
:C!\Phi_h(e),
$$

and every handler reduction preserves this type and bound.

### Proof

`SH-Ret` uses value substitution.  `SH-Match` uses parameter substitution and
Lemma III.1 for $k$.  `SH-Forward` uses the free-request typing rule and the
structural handler-typing induction for its rewrapped continuation.  Reductions
inside the scrutinee use Chapter-II preservation. $\square$

## 2. Affine effect theorem

### Theorem III.3

If $b$ is $\Delta$-free and

$$
\mathsf{FreeCert}(L_B+\Sigma,\widehat E,\mathcal K,\mathsf F_\Sigma(T))
\land\mathsf{AffineCert}(\Delta,h,e')
\land\Gamma\vdash M:A!(b\cdot\Delta\cdot e),
$$

then

$$
\Gamma\vdash
\mathsf{shallow}_\Delta M\ \mathsf{with}\ h
:A!(b\cdot e'\cdot e).
$$

### Proof

On a matching request, residual-context typing identifies the bare tail at
$e$; response sequencing gives $e'\cdot e$, and the already evaluated prefix
contributes $b$.  If the optional request is absent, the computation follows a
path bounded by $b\cdot e$, and

$$
b\cdot e\leq b\cdot e'\cdot e
$$

follows from $1\leq e'$ and monotonicity.  The return rule is identity. $\square$

This theorem is an upper-bound theorem, not an assertion that every run reaches
$\Delta$.

## 3. Operational/denotational commutation

### Theorem III.4

If

$$
\mathsf{FreeCert}(L_B+\Sigma,\widehat E,\mathcal K,\mathsf F_\Sigma(T))
\land\mathsf{HandlerCert}(\Delta,h,\Phi_h),
$$

then, for every closed recursion-free handled computation,

$$
\llbracket
\mathsf{shallow}_\Delta M\ \mathsf{with}\ h
\rrbracket
=
\mathsf{sh}_{\Delta,h}(\llbracket M\rrbracket).
$$

### Proof sketch

Induct on the finite outer base/free structure supplied by `FreeCert`.

- return uses the return equation;
- an internal/base step uses functoriality and Chapter-II soundness;
- a matching request uses semantic substitution for $p$ and $k$;
- a nonmatching request rebuilds the same constructor and uses the induction
  hypothesis pointwise on its rewrapped continuation.

The matching case deliberately does not apply the induction hypothesis to its
bare continuation.  This distinguishes shallow from deep handling.

## 4. Adequacy preservation

### Theorem III.5

Assume

$$
\begin{aligned}
&\mathsf{FreeCert}(L_B+\Sigma,\widehat E,\mathcal K,\mathsf F_\Sigma(T))\\
&\land\mathsf{HandlerCert}(\Delta,h,\Phi_h)
\land\mathsf{TTCert}(S,T,\mathcal O)
\land\mathsf{ConstructorSeparated}(\mathsf{observe}_{\mathsf F})
\land\mathsf{TTClause}_h.
\end{aligned}
$$

Here `TTClause` means, for every operation clause,

$$
p_S\,V_P\,p_T
\land k_S\mathrel{V_R^{\top}}k_T
\Rightarrow
h_S(p_S,k_S)\mathrel{V_C^{\top\top}}h_T(p_T,k_T),
$$

with the analogous value relation for return clauses.

Then ground adequacy is preserved by the shallow handler:
operational returns, base outcomes, matching replacements and forwarded
requests agree with the structural shallow denotation.

### Proof

Combine Theorem III.4 with Chapter-II finite adequacy.  Ordinary clause
computations use the graded TT fundamental lemma; matching clauses use
`TTClause`; forwarded continuations use orthogonality and pole closure.
`observeReflect` converts the final TT relation into adequacy. $\square$

## 5. Conservativity

Adding the handler syntax does not alter reduction or denotation of terms that
do not use it.  Moreover, the affine identity handler is observationally the
identity on computations whose bound contains no matching $\Delta$, subject to
transparent forwarding.

The latter statement does not say that a general handler with a nontrivial
return clause is identity on old programs.

## 6. Chapter-III structure-preservation theorem

### Definition III.1 — `HandlerCert`

For an exhaustive $\Delta$-handler $h$ and
$\Phi_h:\widehat E\to\widehat E$, we say that
$\mathsf{HandlerCert}(\Delta,h,\Phi_h)$ holds when:

1. **Monotonicity.** $\Phi_h$ respects subeffecting.
2. **Return typing.** The return clause has an effect below $\Phi_h(1)$.
3. **Matching typing.** Every operation clause transforms each admissible
   residual bound below the declared output bound.
4. **Transparent forwarding.** A nonmatching operation is rebuilt and the
   handler remains on its continuation.
5. **Relational compatibility.** Clauses preserve both the structural relation
   and the graded TT relation.

Writing $\mathsf{grade}(K)\leq d$ for “$K$ type-checks at an effect below
$d$”, these conditions are

$$
\begin{aligned}
\mathsf{mono}_h:&\quad
e\leq f\Rightarrow\Phi_h(e)\leq\Phi_h(f),\\
\mathsf{return}_h:&\quad
\Gamma,x:A\vdash H_{\mathsf{ret}}:C!r
\land r\leq\Phi_h(1),\\
\mathsf{match}_h:&\quad
\forall i,b,e,d.\ b\cdot\Delta\cdot e\leq d\\
&\Rightarrow
\Bigl(
\Gamma,p:P_i,k:R_i\xrightarrow{e}A
\vdash H_i:C!c_i
\land b\cdot c_i\leq\Phi_h(d)
\Bigr),\\
\mathsf{forward}_h:&\quad
\Gamma'\neq\Delta\Rightarrow
\mathsf{sh}_h(\mathsf{op}_{\Gamma',j}(p,k))\\
&\hspace{25mm}=
\mathsf{op}_{\Gamma',j}
(p,\lambda r.\mathsf{sh}_h(k(r))),\\
\mathsf{structuralClause}_h:&\quad
(p,k)\mathrel{\mathsf{Str}_\Delta(R)}(p',k')
\Rightarrow H_i[p,k]\mathrel{\mathsf{Str}_\Delta(R)}h_i(p',k'),\\
\mathsf{TTClause}_h:&\quad
p_S\,V_P\,p_T\land k_S\mathrel{V_R^{\top}}k_T
\Rightarrow
h_S(p_S,k_S)\mathrel{V_C^{\top\top}}h_T(p_T,k_T).
\end{aligned}
$$

### Definition III.2 — `AffineCert`

The affine response fragment satisfies
$\mathsf{AffineCert}(\Delta,h,e')$ when:

1. $h$ has a clause for every operation in $\Delta$;
2. its return clause is $H_{\mathsf{ret}}=\mathsf{return}\,x$;
3. each response computation has
   $\Gamma,p:P_i\vdash R_i(p):R_i!e'$;
4. each operation clause is
   $H_i\equiv\mathbf{let}\ r\leftarrow R_i(p)\ \mathbf{in}\ k\,r$;
5. $1\leq e'$.

For this fragment, on the domain of grades whose displayed prefix $b$ is
$\Delta$-free,

$$
\Phi_{\Delta,e'}(b\cdot\Delta\cdot e)=b\cdot e'\cdot e.
$$

### Definition III.3 — `ShallowCert`

We say that $\mathsf{ShallowCert}(\Delta,h,\Phi_h)$ holds when:

1. **Safety.** Handler reduction has preservation and effect-aware progress.
2. **Boundary equations.** Return, matching and forwarding satisfy their
   declared operational/semantic equations.
3. **Semantic commutation.** Direct handling agrees with the structural
   shallow map.
4. **Adequacy.** Operational and denotational handled observations agree.
5. **Conservativity and boundary discipline.** Handler-free terms are
   unchanged and one shallow pass stops after its first match.

The principal conditions are

$$
\begin{aligned}
\mathsf{hpres}:&\quad
\Gamma\vdash M:A!e\Rightarrow
\Gamma\vdash\mathsf{shallow}_\Delta(M,h):C!\Phi_h(e),\\
\mathsf{commute}_h:&\quad
\llbracket\mathsf{shallow}_\Delta(M,h)\rrbracket
=\mathsf{sh}_{\Delta,h}(\llbracket M\rrbracket),\\
\mathsf{adequate}_h:&\quad
\mathsf{obs}_{\mathrm{op}}(\mathsf{shallow}_\Delta(M,h))
=\mathsf{obs}_{\mathrm{den}}(\mathsf{sh}_{\Delta,h}(\llbracket M\rrbracket)),\\
\mathsf{conservative}_h:&\quad
M\in L_B+\Sigma\Rightarrow
\llbracket M\rrbracket_{+h}=\llbracket M\rrbracket_{\mathsf F}.
\end{aligned}
$$

### Theorem III.6 — Shallow certificate

Let $P=(L_B+\Sigma,\widehat E,\mathcal K,\mathsf F_\Sigma(T))$.  Assume:

1. $P$ satisfies `FreeCert`;
2. the two compared models and pole satisfy `TTCert`, and the extended pole is
   closed under the $\Sigma$ constructors;
3. either the handler satisfies `AffineCert` with
   $\Phi_h=\Phi_{\Delta,e'}$, or it satisfies the general `HandlerCert`;
4. the free observation separates its constructors.

Then

$$
\mathsf{ShallowCert}(\Delta,h,\Phi_h)
$$

holds.

## 7. What is passed to Chapter IV

The residual-context, rule-analysis and finite-tree inductions are expanded in
[Chapter III — detailed shallow-handler proofs](chapter-3-proof-details-v5.md).

Chapter IV receives the standard shallow continuation interface, not just the
response-only sugar.  Nonmatching continuations already retain the shallow
handler; it recursively wraps matching continuations to derive deep handling.
It must add a recursion principle and
prove the resulting recursive effect bound; neither follows from
`ShallowCert` alone.
