# Nested shallow handler composition v1

## Status

**Derived composition laws, grade bounds, and non-commutation examples for
nested one-shot shallow handlers.**

The result explains what nesting adds without silently turning a shallow
handler into a deep one.

## 1. Two handler specifications

Let

$$
h=(\Delta,c,K),
\qquad
g=(\Gamma,d,J)
$$

be exhaustive handler specifications. Their structural functions are

$$
H_h:\mathsf{GTree}_L(X)
\to
\mathsf{GTree}_{\Phi_{\Delta,K}(L)}(X)
$$

and

$$
H_g:\mathsf{GTree}_{L'}(X)
\to
\mathsf{GTree}_{\Phi_{\Gamma,J}(L')}(X).
$$

The source nesting

```text
handle_Gamma
  (handle_Delta M with c)
with d
```

places $g$ outside $h$.

## 2. Denotation of nesting

### Theorem HC-001 — Nested-handler compositionality

$$
\boxed{
\llbracket
\mathsf{handle}_\Gamma
(\mathsf{handle}_\Delta M\;\mathsf{with}\;c)
\;\mathsf{with}\;d
\rrbracket
=
H_g(H_h(\llbracket M\rrbracket)).
}
$$

### Proof

Apply the compositional denotation of a handler twice. No special nested rule is
needed. $\square$

### Theorem HC-002 — Operational nesting adequacy

For a closed recursion-free term,

$$
\mathsf{Beh}
(\mathsf{handle}_\Gamma
(\mathsf{handle}_\Delta M\;\mathsf{with}\;c)
\;\mathsf{with}\;d)
=
H_g(H_h(\mathsf{Beh}(M))).
$$

### Proof

Apply AD-004 to the outer handler, then to the inner handler. OA-1--OA-5 have
already been discharged by OD-012. $\square$

This equation covers the two characteristic propagation cases:

- an inner handler forwards an other-interface free request without retaining
  itself, after which the outer handler may inspect it;
- a base request retains both pending handler frames in their original nesting
  order until the base machine responds.

## 3. Grade composition

### Theorem HC-003 — Sequential grade bound

If

$$
t\in\mathsf{GTree}_L(X),
$$

then

$$
\boxed{
H_g(H_h(t))
\in
\mathsf{GTree}_{
\Phi_{\Gamma,J}(\Phi_{\Delta,K}(L))}(X).
}
$$

### Proof

FE-014 first gives

$$
H_h(t)\in\mathsf{GTree}_{\Phi_{\Delta,K}(L)}(X).
$$

Apply FE-014 again for $g$. $\square$

Because $\Phi$ is monotone, widening either input or clause grade widens the
composite result monotonically.

The displayed language is a sound upper bound. It need not be the least trace
set of the concrete handled tree: $L$, $K$, and $J$ may already contain
unrealized paths, and each $\Phi$ takes downward closure.

## 4. A sequence of handlers

For a list of handler specifications

$$
\vec h=(h_1,\ldots,h_n),
$$

ordered from innermost to outermost, define

$$
H_{()}=\mathrm{id},
$$

$$
H_{(h_1,\ldots,h_n)}
=
H_{h_n}\circ\cdots\circ H_{h_1},
$$

and the grade transformer

$$
\Phi_{()}=\mathrm{id},
$$

$$
\Phi_{(h_1,\ldots,h_n)}
=
\Phi_{h_n}\circ\cdots\circ\Phi_{h_1}.
$$

### Corollary HC-004

$$
t\in\mathsf{GTree}_L(X)
\Longrightarrow
H_{\vec h}(t)
\in
\mathsf{GTree}_{\Phi_{\vec h}(L)}(X).
$$

### Proof

Induction on the handler list using HC-003. $\square$

List concatenation corresponds to function composition, so association of
nested handler frames is semantically unambiguous. This is an action of the
free monoid of handler specifications on underlying trees, accompanied by a
sound action on grade bounds.

## 5. Same-interface nesting

Let $\Delta$ contain

$$
\mathsf{tick}:1\to1
$$

and let the clause return $*$ purely. Write

$$
t
=
\Delta(\Delta(\mathsf{ret}(*)))
$$

for the tree with two consecutive `tick` nodes.

One shallow handler gives

$$
H_\Delta(t)
=
\Delta(\mathsf{ret}(*)),
$$

because it handles the first node and resumes the continuation without itself.
Applying a second outer handler gives

$$
H_\Delta(H_\Delta(t))
=
\mathsf{ret}(*).
$$

### Proposition HC-005 — Bounded head consumption

$n$ nested pure handlers for the same interface can eliminate at most $n$
successive matching free heads along a path. Base nodes between those heads do
not consume a handler; a different free interface stops the next pending
handler by forwarding.

### Proof

Induction on $n$. Each application of $H_\Delta$ traverses base nodes and either
returns, forwards at the first other-interface node, or removes exactly one
matching $\Delta$ node. $\square$

This resembles a finite-depth handler but is not a deep handler. A deep handler
reinstalls itself recursively in the captured continuation with no fixed bound.

## 6. Same-interface nesting does not collapse

In general there is no clause family $e$ satisfying

$$
H_\Delta^d\circ H_\Delta^c=H_\Delta^e
$$

on all trees. The two-`tick` example is already a counterexample: the left side
can remove both nodes, while every single one-shot handler removes only the
first.

### Corollary HC-006

One-shot handlers for a fixed interface are not idempotent in general:

$$
H_\Delta\circ H_\Delta\neq H_\Delta.
$$

They become idempotent only under a domain restriction ensuring that after the
first application no path exposes another matching $\Delta$ as its first free
head.

## 7. Different interfaces do not commute

Let $\Delta$ and $\Gamma$ each contain a unary unit operation. Let the
$\Delta$ clause produce one $\Gamma$ request before returning, while the
$\Gamma$ clause is pure. On the single-node input

$$
t=\Delta(\mathsf{ret}(*)),
$$

we obtain

$$
H_\Gamma(H_\Delta(t))
=
\mathsf{ret}(*),
$$

but

$$
H_\Delta(H_\Gamma(t))
=
\Gamma(\mathsf{ret}(*)):
$$

the first $H_\Gamma$ sees the other-interface $\Delta$, forwards it, and ends;
the later $H_\Delta$ handles it but leaves the newly produced $\Gamma$ request.

### Theorem HC-007 — Non-commutation

In general,

$$
H_\Gamma\circ H_\Delta
\neq
H_\Delta\circ H_\Gamma,
$$

and correspondingly

$$
\Phi_{\Gamma,J}\circ\Phi_{\Delta,K}
\neq
\Phi_{\Delta,K}\circ\Phi_{\Gamma,J}.
$$

The tree counterexample proves the semantic inequality. For grades, choose
principal languages containing exactly the displayed operation traces and
clause traces; the two orders retain different qualified tokens. $\square$

Non-commutation can occur even when clauses are pure: on a path
$\Delta\Gamma$, handling $\Delta$ first exposes $\Gamma$ to the outer handler,
whereas handling $\Gamma$ first forwards at $\Delta$ and ends before seeing the
later $\Gamma$.

## 8. A sufficient commutation condition

The strongest simple condition is **head separation** on a domain $D$:

1. every $t\in D$ has at most one free node on each path;
2. $\Delta$ clauses introduce no $\Gamma$ node;
3. $\Gamma$ clauses introduce no $\Delta$ node.

### Proposition HC-008

Under head separation,

$$
H_\Gamma(H_\Delta(t))
=
H_\Delta(H_\Gamma(t))
$$

for $t\in D$.

### Proof

Before the sole possible free node, both handlers traverse the same base
prefix. If there is no free node, both return the tree. If the node is
$\Delta$, $H_\Gamma$ forwards and disappears while $H_\Delta$ performs its
clause; the symmetric nesting produces the same clause tree because it cannot
introduce $\Gamma$. The $\Gamma$ case is symmetric; another interface is
forwarded by both. $\square$

This condition is intentionally restrictive. Ordinary sequential programs with
two free requests do not satisfy it, so commutation should not be a default
language law.

## 9. Relation preservation under nesting

### Proposition HC-009

If each paired handler specification satisfies `RelatedClauses`, then a list of
paired nested handlers preserves $\mathsf{TreeRel}$.

### Proof

Induction on the handler list using LR-005. $\square$

Thus nested composition requires no new relational axiom, even though its
effect on traces is ordered and noncommutative.

## 10. Design consequence

Nested shallow handlers form an ordered program construct, not a commutative
set of eliminators. Their natural static semantics is therefore ordered
composition of the $\Phi$ transformers:

$$
L
\xmapsto{h_1}\Phi_{h_1}(L)
\xmapsto{h_2}\Phi_{h_2}(\Phi_{h_1}(L))
\longrightarrow\cdots.
$$

This matches the original noncommutative effect philosophy. No exchange law
should be added unless a restricted commutation theorem such as HC-008 has been
proved for the relevant program domain.
