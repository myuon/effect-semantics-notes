# Typed base interpretation theorem v1

## Status

**Detailed paper proof of the second main-theorem layer in `Set`.**

The theorem constructs the canonical interpretation of **typed base trees** in
an arbitrary base graded monad. It also records why the larger carrier defined
only by a path-language bound cannot be folded into a single base grade without
additional assumptions on the grade monoid.

## 1. Why a typing derivation is needed

Let $\mathsf{BaseTree}(X)$ be the base-only fragment of $\mathsf{GTree}(X)$.
The trace refinement

$$
\{t\mid\mathsf{Tr}(t)\subseteq J(b)\}
$$

says that every complete path has grade at most $b$. This is enough to place the
tree in the trace-language model, but it need not exhibit a common grade $c$ for
all continuations of a root operation such that

$$
|\beta|c\leq_B b.
$$

An arbitrary preordered monoid need not have joins. Consequently, pathwise
boundedness alone does not support a structural definition with codomain
$T_bX$. Source typing supplies exactly the missing factorization data.

This is not a defect of the tree model. It separates two roles:

- trace languages describe runtime path sets and first-free-head handling;
- typed base trees describe computations accepted by the original
  $B$-graded calculus.

## 2. Target base model

Fix a preordered monoid $(B,\cdot,1,\leq_B)$ and a strong $B$-graded monad $T$
on `Set`, consisting of

$$
\eta_X:X\to T_1X,
$$

$$
(-)^*_{b,c}:
(X\to T_cY)\to(T_bX\to T_{bc}Y),
$$

and proof-irrelevant weakening maps

$$
\tau_{b,b'}:T_bX\to T_{b'}X
\qquad(b\leq_Bb').
$$

Assume the usual graded monad laws and

$$
\tau_{b,b}=\mathrm{id},
\qquad
\tau_{b',b''}\tau_{b,b'}=\tau_{b,b''},
$$

together with compatibility of weakening and Kleisli extension.

For every base operation $\beta:P_\beta\to R_\beta$, assume a primitive
interpretation

$$
\beta^T:P_\beta\to T_{|\beta|}R_\beta.
$$

No freeness, injectivity, or carrier isomorphism is assumed of $T$.

## 3. Typed base trees

Write

$$
d:\mathsf{BTree}_b(X)
$$

for a base tree together with a grade derivation. The derivations are generated
by:

### Return

$$
\frac{x:X}{\mathsf{ret}(x):\mathsf{BTree}_1(X)}.
$$

### Base operation

$$
\frac{
p:P_\beta
\qquad
k(r):\mathsf{BTree}_c(X)\quad(r:R_\beta)
}{
\mathsf{base}_\beta(p,k):
\mathsf{BTree}_{|\beta|c}(X)
}.
$$

All response branches have the common upper grade $c$. Individual branches can
first be weakened to $c$.

### Weakening

$$
\frac{d:\mathsf{BTree}_b(X)\qquad b\leq_Bb'}
{\mathsf{wk}_{b,b'}d:\mathsf{BTree}_{b'}(X)}.
$$

Erasing a derivation gives an ordinary base-only tree $|d|$.
When speaking of the graded monad of typed trees, we quotient raw derivations by
the coherence equations listed in Section 6. Until then, equations may be read
as equations modulo that congruence.

### Lemma BI-001 — Trace soundness

If $d:\mathsf{BTree}_b(X)$, then

$$
\mathsf{Tr}(|d|)\subseteq J(b).
$$

### Proof

Induction on $d$. Return uses $1\leq_B1$. At a base node, every continuation
path $m$ satisfies $m\leq_Bc$ by induction, hence
$|\beta|m\leq_B|\beta|c$ by monoidal monotonicity. Weakening composes the path
inequality with $b\leq_Bb'$. $\square$

The converse is not asserted. It requires, for example, suitable joins or an
explicit grade-inference/factorization property of $B$.

## 4. Typed return and bind

Typed bind is defined by induction on its first derivation:

$$
\mathsf{bind}^{\mathsf B}_{b,c}:
\mathsf{BTree}_b(X)
\times
(X\to\mathsf{BTree}_c(Y))
\to
\mathsf{BTree}_{bc}(Y).
$$

At return it uses the right-unit equality $1c=c$. At an operation node it binds
each continuation subtree and reassociates

$$
(|\beta|b')c=|\beta|(b'c).
$$

At weakening it uses monotonicity $b\leq b'\Rightarrow bc\leq b'c$.

### Lemma BI-002 — Erasure

Typed bind erases to ordinary structural tree bind:

$$
|d\mathbin{\mathsf{bind}^{\mathsf B}}f|
=
|d|\mathbin{\mathsf{bind}}(\lambda x.|f(x)|).
$$

### Lemma BI-003 — Typed monad laws

Return and typed bind satisfy left unit, right unit, and associativity after the
canonical monoid reassociations and weakening coherence.

### Proof

Both results follow by induction on $d$. Operation cases apply the induction
hypothesis pointwise. Weakening cases use functoriality of $\mathsf{wk}$ and its
compatibility with typed bind. $\square$

## 5. Canonical typed fold

Define

$$
\mathsf{fold}^T_b:\mathsf{BTree}_b(X)\to T_bX
$$

by induction on the typing derivation:

$$
\mathsf{fold}^T_1(\mathsf{ret}(x))=\eta(x),
$$

$$
\mathsf{fold}^T_{|\beta|c}
(\mathsf{base}_\beta(p,k))
=
\beta^T(p)
\mathbin{\mathsf{bind}^T}
(\lambda r.\mathsf{fold}^T_c(k(r))),
$$

$$
\mathsf{fold}^T_{b'}(\mathsf{wk}_{b,b'}d)
=
\tau_{b,b'}(\mathsf{fold}^T_b(d)).
$$

Every equation is typed without splitting a composite grade.

### Theorem BI-004 — Typed base interpretation

For every target model described in Section 2, the family $\mathsf{fold}^T_b$
is natural in $X$, preserves return and primitive base operations, commutes with
weakening, and preserves typed bind:

$$
\mathsf{fold}^T_{bc}
(d\mathbin{\mathsf{bind}^{\mathsf B}}f)
=
\mathsf{fold}^T_b(d)
\mathbin{\mathsf{bind}^T}
(\lambda x.\mathsf{fold}^T_c(f(x))).
$$

### Proof

Naturality is induction on $d$. Primitive preservation and weakening
compatibility are defining equations.

For bind preservation, induct on $d$.

- Return is the left-unit law of $T$.
- At $\mathsf{base}_\beta(p,k)$, unfold both folds. The left side first folds
  every $k(r)\mathbin{\mathsf{bind}^{\mathsf B}}f$. Apply the induction
  hypothesis to those subtrees, then use associativity of Kleisli bind in $T$.
- At weakening, use compatibility of $\tau$ with bind and the induction
  hypothesis.

The required grade equalities are precisely the unit and associativity
equalities of $B$. $\square$

## 6. What “derivation independence” means here

The fold is invariant under the structural coherence equations generated by:

1. identity weakening;
2. composition of consecutive weakenings;
3. moving weakening through return and bind using the graded-monad coherence
   laws;
4. monoid unit and associativity reassociation.

### Corollary BI-005 — Coherence

If $d$ and $d'$ are identified by those equations, then

$$
\mathsf{fold}^T(d)=\mathsf{fold}^T(d').
$$

### Proof

Check each generating equation using the corresponding law of $T$; closure
under contexts and transitivity then gives the result. $\square$

This does **not** claim that every two unrelated typings of the same erased tree
have equal denotations. Such a theorem needs a principal-grade or coherence
theorem for the source type system. Keeping this boundary explicit prevents a
hidden assumption about joins in $B$.

## 7. Preservation by base-model morphisms

Let $T$ and $U$ be two target base models. A primitive-preserving graded monad
morphism is a natural family

$$
q_b:T_bX\to U_bX
$$

preserving unit, typed bind, weakening, and every primitive:

$$
q_{|\beta|}(\beta^T(p))=\beta^U(p).
$$

### Theorem BI-006 — Morphism lifting

For every $d:\mathsf{BTree}_b(X)$,

$$
\boxed{
q_b(\mathsf{fold}^T_b(d))
=
\mathsf{fold}^U_b(d).
}
$$

### Proof

Induction on $d$.

- Return uses preservation of unit.
- An operation node uses primitive preservation, bind preservation, and the
  induction hypotheses for all response subtrees.
- Weakening uses $q\tau^T=\tau^Uq$ and the induction hypothesis.

$\square$

Thus the typed fold is canonical with respect to changes of base model. This is
the precise form of the earlier informal statement that morphisms “lift through
the free extension” on the base-only fragment.

## 8. Strength and value contexts

Erased base trees have the cartesian strength

$$
\mathsf{st}^{\mathsf B}(a,d)
=
\mathsf{map}(\lambda x.(a,x))(d).
$$

### Proposition BI-007 — Strength preservation

If the primitive interpretations are algebraic and $T$ carries its stated
strength, then

$$
\mathsf{fold}^T
(\mathsf{st}^{\mathsf B}(a,d))
=
\mathsf{st}^T(a,\mathsf{fold}^T(d)).
$$

### Proof

Induction on $d$. Return is the strength-unit law. At an operation node,
algebraicity moves strength through the primitive operation and the induction
hypothesis handles every continuation. Weakening is strength-natural. $\square$

This proposition is what is needed when the base calculus includes products,
function environments, and fine-grain CBV sequencing. It is not needed for the
bare computation-tree fold of BI-004.

## 9. Second-layer theorem

### Theorem BI-008 — Base interpretation layer

An algebraic base signature generates a derivation-indexed free $B$-graded
base-tree model after quotienting by structural coherence. Every strong
$B$-graded monad $T$ with coherent weakening and
grade-correct primitive interpretations receives a canonical typed fold. The
fold preserves return, typed bind, weakening, and primitives; it preserves
strength under the algebraicity assumption; and primitive-preserving graded
monad morphisms commute with it.

### Proof

Combine BI-001--BI-007. $\square$

## 10. Boundary of the theorem

- The theorem gives a fold, not an isomorphism. Writer is a special case where
  the chosen model is itself freely presented by its logging operation.
- The domain is the derivation-indexed base calculus, not every path-bounded
  base tree.
- The theorem interprets the base-only fragment. Free nodes remain visible in
  $\mathsf{GTree}$ so that shallow handlers can inspect their first runtime
  occurrence.
- A direct fold of mixed trees into an arbitrary $T$ would require $T$ itself to
  interpret the free interfaces; doing so before handling would erase the
  structure that the shallow handler must observe.

These restrictions are exactly what lets the theorem avoid the invalid carrier
equality $\mathsf{BaseTree}_bX\cong T_bX$.
