# A sufficient construction of the base action

## Status

**Alternative representation theorem.** The main development now assumes the
standard graded FreeT, whose action is canonical. This page applies when a
chosen implementation externalizes the root grade as a coproduct; it gives a
sufficient condition for that representation to recover the same action.

## 1. Root exposure

Recall

$$
(\mathcal H_A X)_d
=
\coprod_{c\in B}T_c(\mathsf{Step}_{A,X}(c,d)).
$$

Assume that every $T_b$ coherently preserves this displayed coproduct.  Write
the comparison isomorphism as

$$
\chi_{b,X}:
T_b\left(\coprod_{c\in B}X_c\right)
\xrightarrow{\cong}
\coprod_{c\in B}T_bX_c.
\tag{Root-Expose}
$$

Only these grade-indexing coproducts are required; preservation of arbitrary
coproducts is stronger than necessary.  The maps $\chi$ must be natural and
coherent with $\eta^T$, $\mu^T$, weakening and strength.

Left multiplication of an effect bound transports one-step outcomes:

$$
\lambda_{b,c,d}:
\mathsf{Step}_{A,X}(c,d)
\longrightarrow
\mathsf{Step}_{A,X}(b\cdot c,b\cdot d).
\tag{Prefix-Step}
$$

Indeed, $c\le d$ implies $bc\le bd$, while
$c\Delta e\le d$ implies $bc\Delta e\le bd$.  Parameters and continuations
are unchanged.

## 2. Construction

Let

$$
\widehat T:=\mathsf F_\Sigma(T),
\qquad
\alpha_A:\mathcal H_A(\widehat T A)\cong\widehat T A
$$

be the indexed initial-algebra structure.  Define

$$
\begin{aligned}
T_b(\widehat T_dA)
&\xrightarrow{T_b(\alpha^{-1}_{A,d})}
T_b\left(\coprod_cT_c(\mathsf{Step}(c,d))\right)\\
&\xrightarrow{\chi}
\coprod_cT_bT_c(\mathsf{Step}(c,d))\\
&\xrightarrow{\coprod_c\mu^T_{b,c}}
\coprod_cT_{bc}(\mathsf{Step}(c,d))\\
&\xrightarrow{\coprod_cT_{bc}(\lambda_{b,c,d})}
\coprod_cT_{bc}(\mathsf{Step}(bc,bd))\\
&\xrightarrow{\alpha_{A,bd}}
\widehat T_{bd}A.
\end{aligned}
\tag{Construct-Act}
$$

The harmless reindexing of the final coproduct sends the summand named $c$
to the summand named $bc$.

## 3. The sufficient theorem

:::{prf:theorem} Root-exposure construction
:label: thm-root-exposure-base-action-v5

If `(Root-Expose)` is natural and coherent with graded unit,
multiplication, weakening and strength, then `(Construct-Act)` is a coherent
base action.  Consequently the indexed free carrier has graded bind and the
canonical base embedding preserves return and bind.
:::

**Proof.** `Act-Unit` reduces to the unit coherence of $\chi$, the left-unit
law of $T$, and $1c=c$.  For `Act-Mult`, expose the root grades of
$T_bT_c(\widehat T_dA)$ in the two possible orders. Coherence of $\chi$ makes
the exposure squares commute; associativity of $\mu^T$ identifies the maps
into $T_{bce}$; and associativity of grade multiplication identifies their
target indices.  Weakening and strength follow from the corresponding
naturality squares for $\chi$ and $\lambda$.  `Prefix-Step` leaves every free
node and continuation unchanged, which is precisely free-node compatibility.
$\square$

## 4. Morphisms

Suppose $q:T\Rightarrow U$ preserves graded multiplication and commutes with
the two root-exposure maps:

$$
\chi^U\circ q_b\left(\coprod_c X_c\right)
=
\left(\coprod_c q_b(X_c)\right)\circ\chi^T.
\tag{Expose-Morphism}
$$

Naturality of the induced initial-algebra fold then proves `Act-Morphism` by
following `(Construct-Act)` componentwise.  Thus this condition gives a
non-circular, readily checked class of arrows in
$\mathbf{ExtBase}^{\mathrm{str}}_\Delta$.

## 5. What is and is not established

The theorem proves a **sufficient** route to `baseAct` for the external-root
representation. It does not prove
that root exposure is necessary: Writer, State, Exception or another concrete
carrier may admit a direct action even when a chosen categorical presentation
does not preserve the displayed coproduct.

Conversely, the present notes do not yet contain a model having all indexed
initial algebras but admitting no coherent base action at all.  Therefore the
strong independence claim is left open. The main theorem assumes
`StrongGradedFreeT`, which already includes a chosen coherent action. This theorem,
or a direct concrete construction, may discharge that implementation
obligation.
