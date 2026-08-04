# Research synthesis v1

## Status

**Current answer to the original research question.**

The original question was:

> How naturally can a base effect system be extended with free operations and
> shallow handlers while preserving its good properties?

The short answer is:

> A direct, uniform handler extension of an arbitrary opaque graded monad is not
> available in general. A conservative **free interaction refinement followed
> by a typed fold back into the base model** is available, and preserves a broad
> package of algebraic, operational, denotational, and relational properties.

## 1. Starting point

The base language is a recursion-free fine-grain CBV calculus parameterized by:

1. a preordered effect monoid

   $$
   (B,\cdot,1,\leq_B);
   $$

2. algebraic base operations

   $$
   \beta:P_\beta\to R_\beta,
   \qquad |\beta|\in B;
   $$

3. a strong $B$-graded monad $T$ with coherent subeffecting and interpretations
   of the base primitives.

Source operations are simple computations such as $\beta(V)$. They do not take
a source-level continuation argument. Sequencing contexts supply continuations
operationally and denotationally.

## 2. The intended extension

Add qualified free-operation interfaces $\Delta\in\mathcal D$. Effects preserve
the order between base and free behavior through

$$
M=B*\mathcal D^*.
$$

The generator

$$
1\preceq\Delta
$$

reads a free-interface annotation as an optional may-effect. Runtime trees do
not contain padding or subeffect evidence.

Single upper-bound words are insufficient for optional branches and repeated
interfaces. The natural grade algebra is therefore

$$
Q=\mathsf{Down}(M),
$$

with union as joins and down-closed concatenation

$$
L\otimes K
=
\downarrow\{mn\mid m\in L,n\in K\}.
$$

$Q$ is a unital quantale.

## 3. Free interaction layer

The intensional computation model is the well-founded interaction tree

$$
\begin{aligned}
t::={}&\mathsf{ret}(x)\\
&\mid\mathsf{base}_\beta(p,k)\\
&\mid\mathsf{free}_{\Delta,\operatorname{op}}(p,k).
\end{aligned}
$$

Complete execution paths produce words in $M$. Refining trees by a language
bound gives

$$
\widehat T_LX
=
\{t\mid\mathsf{Tr}(t)\subseteq L\}.
$$

This construction provides:

- a strong $Q$-graded monad;
- proof-irrelevant weakening by language inclusion;
- base and free primitive operations;
- an underlying free-monad universal property.

The construction is independent of the internal carrier of the chosen base
model $T$.

## 4. Natural shallow handler

The adopted handler is exhaustive for one interface and inspects the first
**actual** free head exactly once:

$$
H_\Delta(\mathsf{ret}(x))=\mathsf{ret}(x),
$$

$$
H_\Delta(\mathsf{base}_\beta(p,k))
=
\mathsf{base}_\beta(p,\lambda r.H_\Delta(k(r))),
$$

$$
H_\Delta(\mathsf{free}_{\Delta,\operatorname{op}}(p,k))
=
c_{\operatorname{op}}(p)\mathbin{\mathsf{bind}}k,
$$

$$
H_\Delta(\mathsf{free}_{\Gamma,\operatorname{op}}(p,k))
=
\mathsf{free}_{\Gamma,\operatorname{op}}(p,k)
\quad(\Gamma\neq\Delta).
$$

There is no recursive handler call in either free-node equation:

- matching executes the clause and resumes the continuation exactly once,
  without reinstalling the handler;
- another interface is forwarded unchanged and ends the handler.

Base nodes retain the pending handler because they are part of evaluating the
scrutinee toward its first free head.

## 5. Static effect of handling

The general handler type is not a fixed word substitution. It is

$$
H_{\Delta,L,K}:
\widehat T_LX
\to
\widehat T_{\Phi_{\Delta,K}(L)}X.
$$

$\Phi_{\Delta,K}$ acts pathwise:

- base-only path: unchanged;
- first free interface $\Gamma\neq\Delta$: unchanged;
- first free interface $\Delta$: replace that token by a clause trace from $K$.

This rule correctly handles conditionals, optional occurrences, noncommutative
base prefixes, repeated interfaces, and forwarding.

## 6. Recovery of the original word rule

The original-looking rule

$$
b\Delta e\longmapsto bke
$$

is not universally sound. If the displayed optional $\Delta$ is absent at
runtime, a later $\Delta$ in $e$ may become the first actual free head. For
example,

$$
\Delta w\Delta
$$

admits the actual trace $w\Delta$, which handling changes to $wk$, not generally
something below $kw\Delta$.

The simple rule is recovered as a derived rule exactly when every possible
later matching residual $a\Delta t\preceq e$ satisfies the anchoring inequality

$$
bakt\preceq bke.
$$

In particular, it is sound whenever $e$ contains no later $\Delta$.

## 7. Relationship with the original base model

An arbitrary $T_bX$ cannot generally be inspected to determine whether it is a
return or which operation occurs first. Graded multiplication only composes
computations:

$$
T_bT_cX\to T_{bc}X.
$$

It does not provide the inverse decomposition required by a handler. Therefore
the robust construction is two-layered:

```text
free interaction tree
        |
        | typed fold
        v
chosen base graded monad T
```

For a grade derivation carrying residual factorization data, there is a
canonical fold

$$
\mathsf{fold}^T_b:
\mathsf{BTree}_b(X)\to T_bX.
$$

It preserves return, typed bind, weakening, base primitives, and—under the
algebraicity assumptions—strength.

This is a refinement-and-fold extension, not a carrier-level identity
$\mathsf{BaseTree}_bX\cong T_bX$.

## 8. Preserved property package

At paper-proof level, the recursion-free extension preserves or provides:

### Algebraic structure

- quantale effect grades;
- strong graded-monad laws;
- coherent proof-irrelevant subeffecting;
- primitive base/free operations;
- ordered composition of nested handlers.

### Operational metatheory

- substitution and residual-context typing;
- preservation and labelled preservation;
- unique return/internal/base/free decomposition;
- relative determinism;
- hereditary head normalization;
- direct nested-handler behavior.

### Denotational and observational results

- operational behavior-tree adequacy;
- operational/structural handler commutation;
- base observation adequacy through a primitive-preserving comparison
  $q:T\to O$;
- exact Writer and State instances;
- base typing, execution, and denotation conservativity.

### Transformations and relations

- primitive-preserving graded monad morphisms commute with typed folds;
- structural logical relations preserve return, bind, and shallow handling;
- morphism lifting is recovered as the equality-graph special case;
- related base observations transfer through the extension.

## 9. Base conservativity

For an old Stage 0 program:

1. its $B$-typing embeds through the strong monoidal map $J:B\to Q$;
2. its operational execution is literally unchanged;
3. its tree denotation contains no free node;
4. folding gives the original $T$ denotation at first-order results, and the
   appropriate logical relation at higher-order results;
5. wrapping it in any finite sequence of shallow handlers is semantically
   inert.

Thus extension does not require an isomorphism between the free base tree and
the chosen $T$ carrier.

## 10. Nested handlers

Handlers compose in syntactic nesting order:

$$
H_{h_n}\circ\cdots\circ H_{h_1},
$$

with sound grade transformer

$$
\Phi_{h_n}\circ\cdots\circ\Phi_{h_1}.
$$

They are generally:

- not idempotent: two same-interface handlers can consume two successive
  matching heads;
- not commutative: changing interface order changes which later request is
  exposed and handled;
- not collapsible into one shallow handler.

This behavior agrees with the noncommutative base-effect philosophy.

## 11. What was not possible in full generality

### Direct extension of opaque $T$

There is no uniform way to define a first-head handler directly on every graded
monad $T$. A decomposition or free presentation is additional structure.

### Single-word precision

Optionality, repeated interfaces, and noncommutative prefixes require joins of
actual traces. A single principal word is available only under anchoring or
interaction laws.

### Carrier equality

The fold need not be injective, surjective, or invertible. $T$ may quotient
operation trees or contain elements not generated by primitives.

These are mathematical boundaries, not merely unfinished proofs.

## 12. Deferred extensions and their difficulties

### Partial handlers

Handling only some operations of one interface requires operation-level rows,
signature subtraction, or an explicit forwarding summand. Interface-level
token elimination is too coarse.

### Empty-response operations

For $\mathsf{abort}:1\to0$, the current complete-return trace set is empty, so
the dead-end node belongs vacuously to every grade. Carrier-level base purity
therefore needs inhabited response sets. Alternatively one must record maximal
partial paths, which introduces obligations such as $b\preceq bc$ when a
continuation is skipped.

### Recursion

General recursion destroys hereditary normalization. Well-founded trees must be
replaced by coinductive/domain-theoretic trees, and adequacy must include
divergence. The four structural handler equations should remain, but the proof
technology changes.

### Full abstraction

The current result is adequacy and relation preservation. Full abstraction
would require contextual definability and observation-reflection theorems.

## 13. Overall assessment

| Goal | Current outcome |
|---|---|
| Add algebraic free operations | achieved generally in `Set` |
| Add first-head shallow handlers | achieved for exhaustive interfaces |
| Preserve base language | achieved via syntax embedding and typed fold |
| Preserve soundness and adequacy | achieved recursion-free under a small base-observation interface |
| Preserve morphisms and relations | achieved |
| Recover original principal word | achieved under exact anchoring condition |
| Extend arbitrary opaque $T$ directly | impossible without extra decomposition structure |
| Partial handlers | deferred; needs finer effect information |
| Abort/empty responses | deferred; current complete traces are insufficient for carrier reflection |
| General recursion | deferred; requires partial/coinductive semantics |

## 14. Current main claim

The strongest honest summary is:

> Every algebraic base effect system interpreted by a coherent strong graded
> monad admits a conservative free interaction refinement with ordered optional
> free operations and exhaustive first-actual-head shallow handlers. The
> refinement preserves graded structure, recursion-free operational adequacy,
> base observations, morphisms, and logical relations, and returns to the chosen
> base semantics through a typed fold. A uniform carrier-level handler extension
> of an arbitrary opaque graded monad is not available without additional
> decomposition structure.

This boundary—direct carrier extension versus conservative free refinement—is
the central answer produced by the investigation so far.

## 15. Proof map

- construction: [Free extension theorem v1](free-extension-theorem-v1.md)
- fold into $T$: [Typed base interpretation theorem v1](typed-base-interpretation-theorem-v1.md)
- operational adequacy: [Conditional adequacy theorem v1](conditional-adequacy-theorem-v1.md)
- operational obligations: [Operational obligations v1](operational-obligations-v1.md)
- base observation criterion: [Base observation adequacy criterion v1](base-observation-criterion-v1.md)
- logical relations: [Logical relation lifting v1](logical-relation-lifting-v1.md)
- nested handlers: [Nested shallow handler composition v1](nested-shallow-handler-composition-v1.md)
- original word-rule recovery: [Principal-word recovery v1](principal-word-recovery-v1.md)
- conservativity and empty responses: [Base conservativity v1](base-conservativity-v1.md)
