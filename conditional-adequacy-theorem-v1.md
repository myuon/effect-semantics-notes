# Conditional adequacy theorem v1

## Status

**Paper-level proof of the third main-theorem layer, conditional on an adequate
base machine and normalization of the recursion-free source calculus.**

This page separates the theorem that is structural from the assumptions that
belong to a chosen base language or observation. For the fixed recursion-free
calculus, OA-1, OA-2, OA-3, and OA-5 are discharged in
[Operational obligations v1](operational-obligations-v1.md); OA-4 becomes the
definition of a node-compatible base machine.

## 1. Three notions that must not be conflated

There are three semantic comparisons:

1. a source computation and its operational behavior tree;
2. that behavior tree and the compositional $\mathsf{GTree}$ denotation;
3. a base-only tree and its image in a chosen base model $T$.

The shallow handler lives at level 2, where the first actual free node remains
visible. Folding into an opaque $T$ too early may erase precisely that node.

## 2. Operational assumptions

Fix the recursion-free fine-grain CBV calculus and direct shallow-handler rules.
Assume:

### OA-1 — Unique decomposition

Every closed well-typed computation is exactly one of:

- $\mathsf{return}\;V$;
- internally reducible in a unique way;
- suspended at a unique base request $\beta(p;K)$;
- suspended at a unique free request
  $\operatorname{op}_{\Gamma}(p;K)$.

### OA-2 — Typed responses

For $\alpha:P_\alpha\to R_\alpha$, every response supplied to its suspension is
an element of $R_\alpha$.

### OA-3 — Head normalization

Internal reduction reaches one of the three head forms in OA-1. For the present
calculus this follows from recursion-free reducibility. With recursion it must
be replaced by a partial/coinductive statement.

### OA-4 — Base-node fidelity

The base machine exposes $\beta(p;K)$ as the same labelled node
$\mathsf{base}_\beta(p,-)$ used by $\mathsf{GTree}$.

### OA-5 — Clause fidelity

Operational clause evaluation uses the same source computation whose tree
denotation defines $c_{\operatorname{op}}(p)$.

## 3. Operational behavior tree

Define $\mathsf{Beh}(M)$ by well-founded recursion on head normalization:

$$
\mathsf{Beh}(M)=\mathsf{ret}(v)
$$

if $M\longrightarrow^*\mathsf{return}\;V$ and $v=\llbracket V\rrbracket$;

$$
\mathsf{Beh}(M)
=
\mathsf{base}_\beta
(p,\lambda r.\mathsf{Beh}(K(r)))
$$

if $M\longrightarrow^*\beta(p;K)$; and

$$
\mathsf{Beh}(M)
=
\mathsf{free}_{\Gamma,\operatorname{op}}
(p,\lambda r.\mathsf{Beh}(K(r)))
$$

at a free suspension. Internal steps are skipped by the normalization prefix.
OA-1--OA-4 make this definition single-valued and well founded.

### Lemma AD-001 — Internal invariance

If $M\longrightarrow M'$, then

$$
\mathsf{Beh}(M)=\mathsf{Beh}(M').
$$

### Proof

Both computations have the same unique head-normalization sequence after
removing its first internal step. $\square$

## 4. Fundamental tree lemma

Use the structural denotation from the Free extension theorem:

$$
\llbracket M\rrbracket_\rho\in
\mathsf{GTree}(\llbracket A\rrbracket).
$$

For open higher-order terms, define the usual logical relation simultaneously:

- base values are related by equality;
- functions map related values to related computations;
- a computation is related to a tree when its operational behavior tree equals
  that tree.

### Lemma AD-002 — Fundamental lemma

If $\Gamma\vdash M:A!L$ and an environment substitution $\gamma$ is related to
$\rho\in\llbracket\Gamma\rrbracket$, then

$$
\mathsf{Beh}(M\gamma)
=
\llbracket M\rrbracket_\rho.
$$

### Proof

Simultaneous induction on the typing derivation and the handler-commutation
statement AD-004.

- Return is the value fundamental lemma.
- Sequencing uses the exact value-labelled bind equation FE-008: each returned
  value selects the corresponding operational and denotational continuation.
- A base primitive uses OA-4.
- A free primitive is the corresponding free node by definition.
- Branching follows the selected value branch on both sides.
- Subeffecting changes only the grade witness.
- The handler case uses the simultaneously established AD-004 instance; its
  clause premises are smaller typing derivations.

Function introduction and application use the logical-relation clauses. Since
there is no recursion, the proof is well founded on typing plus normalization.
$\square$

### Theorem AD-003 — Intensional behavior-tree adequacy

For every closed well-typed computation,

$$
\boxed{
\mathsf{Beh}(M)=\llbracket M\rrbracket.
}
$$

This is AD-002 in the empty environment. It is stronger than equality of one
ground result: it retains every base/free request and response continuation.

## 5. Handler commutation

Let $H_\Delta$ be exhaustive, and let $c$ be the tree denotation of its clauses.

### Lemma AD-004 — Operational/structural handler commutation

$$
\boxed{
\mathsf{Beh}
(\mathsf{handle}_\Delta M\;\mathsf{with}\;H_\Delta)
=
H_\Delta^c(\mathsf{Beh}(M)).
}
$$

### Proof

Well-founded induction on $\mathsf{Beh}(M)$, simultaneous with AD-002 for the
strictly smaller clause derivations.

1. At return, the direct handler returns the same value and disappears.
2. At a base node, `S-Handle-Base` retains the pending handler in every response
   continuation. Apply the induction hypothesis pointwise.
3. At a matching free node, the direct rule evaluates the clause and then
   resumes the captured continuation exactly once, without reinstalling the
   handler. By OA-5 and exact bind traces, its behavior is

   $$
   c_{\operatorname{op}}(p)\mathbin{\mathsf{bind}}k.
   $$

4. At another free interface, `S-Handle-Free-Other` forwards the unchanged
   request and continuation and ends the handler. This is exactly the unchanged
   free-node equation.

These are all possible heads by OA-1. $\square$

### Corollary AD-005 — Handler adequacy and grade soundness

If $\mathsf{Tr}(\llbracket M\rrbracket)\subseteq L$ and the clauses have common
bound $K$, then

$$
\mathsf{Tr}
(\mathsf{Beh}(\mathsf{handle}_\Delta M\;\mathsf{with}\;H_\Delta))
\subseteq
\Phi_{\Delta,K}(L).
$$

Use AD-003, AD-004, and FE-014.

## 6. Transport to a chosen base model

Let $\mathcal O$ be a set of ground observations. Suppose a base-only
operational computation has observation function

$$
\mathsf{obs}_{\mathrm{op}}:\mathsf{BTree}_b(G)\to\mathcal O,
$$

and $T$ has

$$
\mathsf{obs}_T:T_b\llbracket G\rrbracket\to\mathcal O.
$$

### BA — Base observation adequacy

Assume for every typed base tree $d$,

$$
\mathsf{obs}_{\mathrm{op}}(d)
=
\mathsf{obs}_T(\mathsf{fold}^T(d)).
$$

For a yes/no contextual observation one may instead assume reflection and
preservation separately. Writer satisfies BA with the ordered log and returned
ground value. A reusable sufficient condition, together with Writer and State
instances, is proved in
[Base observation adequacy criterion v1](base-observation-criterion-v1.md).

### Theorem AD-006 — Conditional target adequacy

Let $M:G!J(b)$ be closed. Assume its behavior contains no free node and its
typing induces $d_M:\mathsf{BTree}_b(\llbracket G\rrbracket)$. Then

$$
\boxed{
\mathsf{obs}_{\mathrm{op}}(M)
=
\mathsf{obs}_T
(\mathsf{fold}^T_b(d_M)).
}
$$

### Proof

AD-003 identifies the operational behavior with the erased tree denotation.
BI-001 and the source typing derivation provide $d_M$. Apply BA. $\square$

The no-free-node premise is essential for a base-only observation. A program
that forwards an unhandled free request has a free-head observation instead of
a $T$ observation.

## 7. Adequacy after shallow handling

Suppose handling eliminates all free nodes that can occur on every runtime path
of $M$, so the handled behavior is base-only and has a typed derivation
$d_H:\mathsf{BTree}_{b'}(G)$.

### Theorem AD-007 — Handled-program adequacy

Under OA-1--OA-5 and BA,

$$
\mathsf{obs}_{\mathrm{op}}
(\mathsf{handle}_\Delta M\;\mathsf{with}\;H_\Delta)
=
\mathsf{obs}_T(\mathsf{fold}^T_{b'}(d_H)).
$$

### Proof

AD-004 identifies the operational handled behavior with the structural handler
tree. The assumed elimination makes that tree base-only. Apply AD-006. $\square$

One shallow handler need not eliminate later $\Delta$ nodes or another
interface. Therefore “the handler is exhaustive” does not by itself imply the
base-only premise; exhaustiveness concerns operations at the inspected
interface head, not all future effects.

## 8. Third-layer theorem

### Theorem AD-008 — Conditional adequacy layer

For the recursion-free calculus satisfying OA-1--OA-5:

1. operational behavior trees equal compositional $\mathsf{GTree}$ denotations;
2. direct shallow handling commutes with the structural first-free-head handler;
3. trace-language effect bounds are operationally sound;
4. any adequate chosen base model $T$ receives ground adequacy through the typed
   fold, before or after handling whenever the resulting tree is base-only.

### Proof

Combine AD-003--AD-007. $\square$

## 9. Exact boundary

- OA-1--OA-5 are obligations of the fixed operational calculus, not consequences
  of an arbitrary graded monad.
- BA is a property of the chosen base model and observation.
- Recursion requires divergence observations and coinductive/domain-theoretic
  trees; it is not covered here.
- The theorem proves adequacy, not full abstraction.
- It does not claim every language-grade tree has a single-word typed fold.

These boundaries explain exactly which parts of the Writer proof generalize
structurally and which parts remain assumptions about the base language.
