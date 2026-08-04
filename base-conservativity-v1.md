# Base conservativity v1

## Status

**Paper-level conservativity theorem for the base syntax and typed fold, plus a
counterexample to unrestricted carrier-level purity when operation response
sets may be empty.**

## 1. Three different conservativity claims

The phrase “base conservativity” can mean:

1. **syntactic conservativity:** old base programs retain their typing and
   operational behavior;
2. **denotational conservativity:** interpreting an old program in the free tree
   model and folding it into $T$ recovers its old $T$ denotation;
3. **carrier reflection:** every tree at a principal base grade $J(b)$ is
   base-only.

The first two hold under the established assumptions. The third needs an
additional inhabited-response condition because grades currently record
complete return paths.

## 2. Free-token monotonicity

Let $\#_{\mathcal D}(m)$ be the number of free-interface factors in the normal
form of $m\in M=B*\mathcal D^*$.

### Lemma BC-001

If

$$
m\preceq n,
$$

then

$$
\#_{\mathcal D}(m)
\leq
\#_{\mathcal D}(n).
$$

### Proof

By PW-001, moving downward in the preorder deletes free tokens and lowers base
factors; neither operation increases their number. $\square$

### Corollary BC-002 — Base-word reflection

If $m\preceq b$ for $b\in B$, then $m\in B$. In particular,

$$
J(b)\subseteq B
$$

under the embedding $B\hookrightarrow M$.

Thus the optional inequalities $1\preceq\Delta$ permit insertion of free
tokens into an upper bound, but never permit a free-containing actual word to
be weakened back to a base-only bound.

## 3. Embedding base typing into language grades

Embed a base grade by

$$
J_B(b)=J(b)\in Q.
$$

FE-004 gives

$$
J_B(1)=I,
$$

$$
J_B(bc)=J_B(b)\otimes J_B(c),
$$

and

$$
b\leq_Bc
\Longrightarrow
J_B(b)\subseteq J_B(c).
$$

### Theorem BC-003 — Typing conservativity

Every Stage 0 derivation

$$
\Gamma\vdash_B M:A!b
$$

embeds into a free-extension derivation

$$
\Gamma\vdash_Q M:A!J(b)
$$

without changing the source term.

### Proof

Induction on the typing derivation. Return uses $J(1)=I$, sequencing uses strong
monoidality $J(bc)=J(b)\otimes J(c)$, base primitives retain grade
$J(|\beta|)$, and subeffecting uses monotonicity of $J$. Value, branch, and
function rules are unchanged. $\square$

No converse for arbitrary extended syntax is claimed: a free operation can be
handled away, producing an extended term with a base-only result grade.

## 4. Operational conservativity

### Theorem BC-004

For a Stage 0 term $M$, the internal reductions, base suspensions, and base
machine transitions are identical whether $M$ is regarded as a Stage 0 term or
as a Stage 2 term.

### Proof

The new principal rules require a free-operation or handler constructor, neither
of which occurs in $M$. The old evaluation contexts and principal rules are
unchanged. Hence unique decomposition and every successor configuration agree
by induction on execution length. $\square$

This is literal operational conservativity, not merely observational
equivalence.

## 5. Tree interpretation of base syntax

Let

$$
\llbracket M\rrbracket_{\mathsf B}
$$

be the compositional interaction-tree interpretation of a Stage 0 term. It uses
only `ret`, structural bind, and $\mathsf{base}_\beta$ nodes.

### Lemma BC-005 — Syntactic base purity

$\llbracket M\rrbracket_{\mathsf B}$ contains no free node.

### Proof

Induction on syntax. No Stage 0 constructor introduces a free node, and map and
bind preserve the base-only fragment. $\square$

For a closed computation with first-order result type $G$, the original
$B$-typing derivation supplies a typed base tree

$$
d_M:\mathsf{BTree}_b(\llbracket G\rrbracket)
$$

whose erasure is $\llbracket M\rrbracket_{\mathsf B}$.

## 6. Recovery of the original denotation

Let $G$ be first-order, so its value-set interpretation is the same in the tree
and target models. Let

$$
\llbracket M\rrbracket_T
\in
T_b\llbracket G\rrbracket
$$

be the original Stage 0 denotation in the chosen strong graded monad $T$.

### Theorem BC-006 — Ground/first-order denotational conservativity

$$
\boxed{
\mathsf{fold}^T_b(d_M)
=
\llbracket M\rrbracket_T.
}
$$

### Proof

Use the standard type-indexed logical relation between the tree interpretation
and the $T$ interpretation:

- primitive first-order values are related by equality;
- products and sums are related componentwise;
- functions are related when they send related arguments to computations whose
  typed tree fold is related to the target computation.

The fundamental lemma is simultaneous induction on value and computation
typing.

- Return is the fold unit equation.
- Base primitives are preserved by definition of $\mathsf{fold}^T$.
- Sequencing uses BI-004, which says the fold preserves typed bind.
- Subeffecting uses fold/weakening compatibility.
- Abstraction and application use the function clause; open value contexts use
  BI-007, naturality, and strength preservation.
- Conditionals and cases select/fold the same branch and use naturality of the
  relevant coproduct maps.

At the closed first-order result $G$, the value relation is equality, yielding
the displayed equation. $\square$

For higher-order result types, the conclusion is this logical relation rather
than literal equality: the two function-value carriers mention different
computation models. LR-007 supplies the corresponding relational fold theorem.

Thus the free tree is a conservative refinement of the original denotation. It
need not be isomorphic to $T$.

## 7. Handlers are inert on base trees

### Lemma BC-007

For every base-only tree $t$ and every handler specification $h$,

$$
H_h(t)=t.
$$

### Proof

Induction on $t$. Return is fixed. At a base node, $H_h$ preserves the root and
the induction hypothesis fixes every continuation subtree. There is no free
case. $\square$

### Lemma BC-008 — Base-grade transformer identity

For every $b\in B$,

$$
\Phi_{\Delta,K}(J(b))=J(b).
$$

### Proof

BC-002 says every $m\in J(b)$ is base-only. Hence
$\phi_{\Delta,K}(m)=\{m\}$. Taking the union and downward closure returns the
already downward-closed set $J(b)$. $\square$

### Corollary BC-009 — Handler inertness for base programs

Wrapping a Stage 0 program in any finite sequence of shallow handlers changes
neither its behavior tree nor its language grade:

$$
H_{\vec h}(\llbracket M\rrbracket_{\mathsf B})
=
\llbracket M\rrbracket_{\mathsf B}.
$$

Operationally, each handler persists across base requests, then disappears at
the final return. It never selects a clause.

## 8. Empty-response counterexample

Carrier reflection needs more care. Suppose a free interface contains a
nullary-result operation

$$
\mathsf{abort}:1\to0.
$$

Its tree is

$$
t=\mathsf{free}_{\Delta,\mathsf{abort}}(*,k),
$$

where $k:0\to\mathsf{GTree}(X)$ is the empty function. Under the current
**complete return path** definition,

$$
\mathsf{Tr}(t)=\varnothing.
$$

Consequently,

$$
t\in\mathsf{GTree}_L(X)
$$

for every language $L$, including $J(b)$. Yet $t$ visibly contains a free node.

### Proposition BC-010 — Failure of unrestricted carrier reflection

Without an inhabited-response assumption, the implication

$$
t\in\mathsf{GTree}_{J(b)}(X)
\Longrightarrow
t\text{ is base-only}
$$

is false.

This does not invalidate FE-017's graded-monad laws or BC-003--BC-009. It shows
that complete return traces do not observe dead-end requests.

## 9. Carrier reflection with inhabited responses

Assume every base and free operation response set is inhabited.

### Lemma BC-011 — Every node lies on a complete path

Every node of a well-founded interaction tree lies on a path ending at a
return.

### Proof

Reach the chosen node by its finite address. From it, choose one response at
each operation node. Well-foundedness prevents an infinite descending branch,
so the choices eventually reach a return. Inhabited response sets ensure a
choice is available at every node. $\square$

### Theorem BC-012 — Principal base carrier reflection

Under inhabited responses,

$$
t\in\mathsf{GTree}_{J(b)}(X)
\Longrightarrow
t\text{ is base-only}.
$$

### Proof

If $t$ contained a free node, BC-011 would extend it to a complete path. That
path's word would contain a free token, but membership in $J(b)$ and BC-002 say
every complete path word is base-only, a contradiction. $\square$

The converse is not automatic: a base-only tree can have path grades not
bounded by the particular $b$.

## 10. Alternative repair: observe maximal partial paths

Instead of assuming inhabited responses, one could grade maximal paths ending
either in a return or in a dead-end request. Then `abort` contributes its
$\Delta$ token.

However, this change exposes a second design obligation. If a computation
aborts before its continuation, typed sequencing declares grade $bc$ while the
maximal partial trace may have only grade $b$. Bounding it requires

$$
b\preceq bc,
$$

which follows from $1\preceq c$ but not from an arbitrary preordered monoid.
Thus maximal-path grading naturally belongs to a may-effect system whose unit
is below every possible continuation effect, or to a richer outcome-sensitive
grade system.

For the current recursion-free calculus without empty response types, complete
return traces are sufficient. Nullary operations should not be added silently;
they require choosing between the inhabited-response restriction and this
maximal-path refinement.

## 11. Conservativity theorem

### Theorem BC-013

For every Stage 0 program:

1. base typing embeds strongly monoidally through $J$;
2. operational execution is unchanged in Stage 2;
3. the free tree denotation is base-only;
4. at first-order results, folding that tree into $T$ recovers the original
   denotation; at higher-order results it satisfies the type-indexed logical
   relation;
5. any finite nesting of shallow handlers is semantically inert.

If operation responses are inhabited, the stronger carrier-level statement
also holds: every element at principal base grade $J(b)$ is base-only.

### Proof

Combine BC-003--BC-009 and, for the final statement, BC-012. $\square$

## 12. Design consequence

The free extension is conservative in the sense needed for modular language
extension without requiring

$$
\mathsf{BaseTree}_bX\cong T_bX.
$$

The correct comparison is the denotation-preserving fold. Carrier equality is
both unnecessary and, with dead-end operation nodes, potentially false for
reasons independent of quotient equations in $T$.
