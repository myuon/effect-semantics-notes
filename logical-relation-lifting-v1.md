# Logical relation lifting v1

## Status

**Paper-level proof that structural relations lift through free trees, typed
base folds, and exhaustive one-shot shallow handlers.**

This is the relational generalization of the morphism comparison theorem.

## 1. Relational signatures

Consider left and right interpretations of the same qualified operation names.
For each base or free operation $\alpha$, fix relations

$$
P_\alpha\subseteq P_\alpha^L\times P_\alpha^R,
\qquad
R_\alpha\subseteq R_\alpha^L\times R_\alpha^R.
$$

Paired base operations have the same grade $|\beta|\in B$; paired free
operations belong to the same interface token $\Delta$. Equality is the common
special case for both parameter and response relations.

Let $R\subseteq X\times Y$ be a relation on returned values.

## 2. Structural tree relation

Define

$$
t\;\mathsf{TreeRel}(R)\;u
$$

inductively by the following clauses.

### Returns

$$
\frac{x\mathrel R y}
{\mathsf{ret}(x)\;\mathsf{TreeRel}(R)\;\mathsf{ret}(y)}.
$$

### Base nodes

$$
\frac{
p\mathrel{P_\beta}p'
\qquad
\forall r\mathrel{R_\beta}r'.\;
k(r)\;\mathsf{TreeRel}(R)\;k'(r')
}{
\mathsf{base}_\beta(p,k)
\;\mathsf{TreeRel}(R)\;
\mathsf{base}_\beta(p',k')
}.
$$

### Free nodes

Use the identical rule for
$\mathsf{free}_{\Delta,\operatorname{op}}$, requiring the same qualified
operation and its chosen parameter/response relations.

Different root constructors or different qualified operations are unrelated.
The universal continuation premise ensures that any pair of related machine
responses selects related subtrees.

### Lemma LR-001 — Identity and composition

If all operation relations are equality, then

$$
\mathsf{TreeRel}(=)
=
=
$$

on well-founded trees. More generally, identity operation relations give an
identity lifting, and relational composition of signatures is contained in
composition of their tree liftings.

### Proof

The identity statement is well-founded induction in both directions.
Composition is proved by induction through a chosen intermediate related tree;
matching root constructors determine its unique operation label. $\square$

The composition statement can be strict when response relations lack suitable
choice/totality properties, so equality is not claimed without extra
assumptions.

## 3. Functor and bind compatibility

### Lemma LR-002 — Map

If

$$
\forall x\mathrel R y.\;f(x)\mathrel S g(y),
$$

then

$$
t\;\mathsf{TreeRel}(R)\;u
\Longrightarrow
\mathsf{map}(f)t\;\mathsf{TreeRel}(S)\;\mathsf{map}(g)u.
$$

### Lemma LR-003 — Bind

If

$$
t\;\mathsf{TreeRel}(R)\;u
$$

and

$$
\forall x\mathrel R y.\;
f(x)\;\mathsf{TreeRel}(S)\;g(y),
$$

then

$$
t\mathbin{\mathsf{bind}}f
\;\mathsf{TreeRel}(S)\;
u\mathbin{\mathsf{bind}}g.
$$

### Proofs

Induction on the derivation of $t\;\mathsf{TreeRel}(R)\;u$. Return applies the
function hypothesis. At either operation node, preserve the paired root and
apply the induction hypothesis to every pair of related responses. $\square$

Thus $\mathsf{TreeRel}$ is a relator for the underlying free interaction-tree
monad.

## 4. Grades

Because paired nodes have the same base grade or interface token, related paths
have the same word in $M=B*\mathcal D^*$.

### Lemma LR-004 — Trace agreement

If $t\;\mathsf{TreeRel}(R)\;u$, then every pair of paths obtained by choosing
related responses has the same trace word. If each response relation is left-
and right-total, every path on either side can be paired, and the unlabelled
trace sets are equal:

$$
\mathsf{Tr}(t)=\mathsf{Tr}(u).
$$

Without totality, equality is restricted to paths whose response choices are
related. The ungraded relation and all compatibility theorems remain valid.

For the main same-signature/equality-response instance, trace equality is
automatic. It restricts the relation to every common language grade:

$$
\mathsf{TreeRel}_L(R)
\subseteq
\widehat T_LX\times\widehat T_LY.
$$

Weakening from $L$ to $K$ is relationally the identity on underlying trees.

## 5. Shallow-handler compatibility

Fix an interface $\Delta$. Let left and right exhaustive clause families be
$c^L$ and $c^R$. Assume for every operation and related parameter pair,

$$
p\mathrel{P_{\operatorname{op}}}p'
\Longrightarrow
c^L_{\operatorname{op}}(p)
\;\mathsf{TreeRel}(R_{\operatorname{op}})\;
c^R_{\operatorname{op}}(p').
\tag{RelatedClauses}
$$

The clause result relation is the operation response relation because the
clause computes the replacement response passed to the captured continuation.

### Theorem LR-005 — Handler relation preservation

If

$$
t\;\mathsf{TreeRel}(R)\;u,
$$

then

$$
H_\Delta^{c^L}(t)
\;\mathsf{TreeRel}(R)\;
H_\Delta^{c^R}(u).
$$

### Proof

Induction on the tree-relation derivation.

- Related returns remain related returns.
- At a base node, both handlers recurse. Apply the induction hypothesis to
  every pair of related response continuations.
- At a matching free node, `RelatedClauses` relates the clause trees. The node
  premise relates the captured continuations for every related replacement
  response. Apply LR-003.
- At another free interface, neither handler recurses; the original related
  nodes are returned unchanged.

$\square$

The matching proof contains no induction hypothesis below the matching free
node. This is the relational form of shallowness.

### Corollary LR-006 — Graded handler relation

In the equality-response instance, if the two clause families share grade bound
$K$ and the inputs share bound $L$, the outputs are related at

$$
\Phi_{\Delta,K}(L).
$$

This combines LR-005 with FE-014; relation preservation and grade preservation
are separate arguments.

## 6. Relations between base models

Let $T$ and $U$ be coherent $B$-graded monads. A **graded computation
relation** assigns to every value relation $R\subseteq X\times Y$ a relation

$$
\overline{T,U}_b(R)
\subseteq
T_bX\times U_bY.
$$

Assume:

### Unit

$$
x\mathrel R y
\Longrightarrow
\eta^T(x)\mathrel{\overline{T,U}_1(R)}\eta^U(y).
$$

### Bind

If

$$
t\mathrel{\overline{T,U}_b(R)}u
$$

and, for every $x\mathrel R y$,

$$
f(x)\mathrel{\overline{T,U}_c(S)}g(y),
$$

then

$$
t\mathbin{\mathsf{bind}^T}f
\mathrel{\overline{T,U}_{bc}(S)}
u\mathbin{\mathsf{bind}^U}g.
$$

### Weakening

For $b\leq b'$, related elements remain related after applying
$\tau^T_{b,b'}$ and $\tau^U_{b,b'}$.

### Primitives

For every paired base parameter,

$$
p\mathrel{P_\beta}p'
\Longrightarrow
\beta^T(p)
\mathrel{\overline{T,U}_{|\beta|}(R_\beta)}
\beta^U(p').
$$

Strength compatibility may be added when proving the open-term fundamental
lemma with product environments; it is not needed for the bare tree fold.

## 7. Relational typed folds

Typed left and right base trees are related by a derivation-indexed version of
$\mathsf{TreeRel}$: paired constructors use the same grade multiplication, and
paired weakening steps use the same endpoint inequality. This supplies a common
declared grade $b$.

### Theorem LR-007 — Fold relation theorem

If

$$
d_L\;\mathsf{BTreeRel}_b(R)\;d_R,
$$

then

$$
\boxed{
\mathsf{fold}^T_b(d_L)
\mathrel{\overline{T,U}_b(R)}
\mathsf{fold}^U_b(d_R).
}
$$

### Proof

Induction on the typed tree-relation derivation.

- Return uses the unit axiom.
- A base node uses the primitive axiom followed by bind compatibility and the
  induction hypotheses for all related response subtrees.
- Weakening uses weakening compatibility.

$\square$

As in BI-005, quotienting typing derivations requires the computation relation
to respect the same structural coherence equations.

## 8. Graph relations recover morphisms

Let $q:T\Rightarrow U$ be a primitive-preserving graded monad morphism. Define

its equality graph by

$$
t\mathrel{\mathsf{Graph}(q_b)}u
\quad\Longleftrightarrow\quad
q_b(t)=u.
$$

### Proposition LR-008

$\mathsf{Graph}(q)$ satisfies the Unit, Bind, Weakening, and Primitive axioms
for equality value relations.

### Proof

Each axiom is exactly the corresponding preservation equation for $q$.
$\square$

Applying LR-007 to two copies of the same typed tree gives

$$
q_b(\mathsf{fold}^T_b(d))
=
\mathsf{fold}^U_b(d),
$$

which is BI-006. Thus morphism lifting is genuinely the equality-graph special
case of relational fold lifting.

## 9. Relational observations

Let $O^L,O^R$ be operational base models equipped with a computation relation,
and let final observations be related by

$$
\mathcal O\subseteq\mathcal O_L\times\mathcal O_R.
$$

If the final observation maps preserve the computation relation, LR-007 yields
related operational observations of related typed base programs. Combining
this with AD-003 and LR-005 gives the same result for programs containing free
operations and shallow handlers, whenever the final handled behaviors are
base-only.

### Theorem LR-009 — Relational adequacy transfer

Related environments and related exhaustive clauses produce related behavior
trees. If their final trees are typed base-only and the two base folds satisfy
the computation-relation axioms, their ground observations are related.

### Proof

The source fundamental lemma uses LR-002, LR-003, and LR-005. Operational/tree
adequacy is AD-003. Fold transport is LR-007, followed by the assumed observation
map compatibility. $\square$

This theorem supports representation independence and compiler-correctness
arguments; exact equality adequacy is its diagonal special case.

## 10. Boundaries

- Related operations must agree on their grade/interface labels, or a separate
  grade translation must be supplied.
- Trace-set equality needs total response relations; handler relation
  preservation itself does not.
- A relation compatible with unit and bind but not primitives cannot validate
  source operation terms.
- Full abstraction additionally needs observation reflection and contextual
  definability.

The structural free layer adds no new relational axiom beyond related
operations, bind compatibility, and related exhaustive clauses.
