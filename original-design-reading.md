# Reading of the original design

## Status

**Source-guided interpretation, not an endorsement of every original assumption.**

This page reads Definition 21 and Remark 22 from the supplied thesis excerpt to identify the intended language-design philosophy. The goal is to preserve that philosophy while repairing unclear or overly strong mathematics.

## 1. Evidence in Definition 21

The original $\Delta$-extension requires

$$
\widehat T_b=T_b
$$

for base grades, primitive operation morphisms of shape

$$
\mathsf{op}^i:
\alpha\times(\beta\to A)
\to\widehat T_\Delta A,
$$

and a handler

$$
H_\Delta:
\widehat T_{b\cdot\Delta\cdot e}A
\to
\widehat T_{b\cdot e'\cdot e}C.
$$

The decisive equation is

$$
H_\Delta
\circ
\widehat T_{b\cdot e\leq b\cdot\Delta\cdot e}
=
(c_{\mathsf{val}})^\sharp.
\tag{Original-Value}
$$

The matching-operation equation is

$$
H_\Delta\circ\mathsf{op}^i
=c_{\mathsf{op}}.
\tag{Original-Op}
$$

## 2. What `Original-Value` implies

The morphism

$$
\widehat T_{b\cdot e\leq b\cdot\Delta\cdot e}
$$

is an explicit semantic coercion from a computation with no $\Delta$ layer to one whose annotation contains $\Delta$.

Taking empty surrounding segments gives the intended generator

$$
1\leq\Delta.
$$

Therefore the original system does not treat a $\Delta$ token as proof that an operation definitely occurs. It treats $\Delta$ as an upper-bound/optional layer.

This rules out the exact-only interpretation as a faithful reading of the original language design.

## 3. The two intended handler cases

The equations specify an exhaustive two-way behavior at the designated $\Delta$ layer.

### No matching operation

A computation from grade $b\cdot e$ may be coerced to $b\cdot\Delta\cdot e$. Handling that coerced computation must agree with the lifted value clause

$$
(c_{\mathsf{val}})^\sharp.
$$

Thus the inserted layer is silent operationally but is not meaningless: when eliminated, it selects the value/no-operation behavior.

### Matching operation

An actual operation injection must be sent to the corresponding operation clause:

$$
H_\Delta\circ\mathsf{op}^i=c_{\mathsf{op}}.
$$

This is precisely the universal behavior expected from a skip-or-operation layer.

## 4. Corresponding polynomial presentation

The direct polynomial candidate matching these two equations is

$$
\mathsf{Layer}_\Delta Z
=
Z+\mathsf{Op}_\Delta Z.
$$

At grade $b\Delta e$:

$$
\widehat T_{b\Delta e}A
\simeq
T_b\left(
\widehat T_eA
+
\mathsf{Op}_\Delta(\widehat T_eA)
\right).
$$

Then:

- the subeffect coercion $be\leq b\Delta e$ uses the left injection;
- the primitive operation uses the right injection;
- $H_\Delta$ is determined by its action on the two injections.

Remark 22's end formula appears to be a Church/handler encoding of the same intended eliminability: an element of $\widehat T_{b\Delta e}A$ is characterized by how it responds to a value clause and all operation clauses. The formula should not be adopted without checking variance, existence of the end, effect ordering, and naturality.

## 5. A subtlety in $(c_{\mathsf{val}})^\sharp$

The original target grade is displayed as

$$
b\cdot e'\cdot e,
$$

not the ordinary post-composition order

$$
b\cdot e\cdot e'.
$$

Thus $(c_{\mathsf{val}})^\sharp$ cannot be assumed to be ordinary Kleisli extension of a completed $be$ computation unless additional commutation is available.

The apparent intention is positional:

> Eliminating the virtual $\Delta$ boundary replaces that boundary by the clause effect $e'$, while preserving the residual tail $e$ after it.

This is a layer-local lifting, not automatically the usual monadic bind. It is one of the original definition's strongest and least justified assumptions, and must be reconstructed from the operational semantics rather than accepted as notation.

## 6. What the excerpt does not establish

The supplied definition does **not** by itself specify:

- how a $\Gamma$ operation with $\Gamma\neq\Delta$ is forwarded;
- whether a forwarded mismatching operation reinstalls the handler around its continuation;
- whether padding proofs are observable or proof-irrelevant;
- how two insertions $\Delta\to\Delta\Delta$ are made coherent;
- whether the end in Remark 22 exists in the intended category;
- whether the displayed handler operations are natural in all objects and grades;
- how $(c_{\mathsf{val}})^\sharp$ is constructed.

Therefore `otherwise` forwarding is philosophically compatible with the design, but is not evidence supplied by Definition 21 itself.

## 7. Faithful reconstruction versus literal reconstruction

### Preserve

The reconstructed language should preserve:

1. base conservativity $\widehat T_b=T_b$;
2. optional free effects via $1\to\Delta$;
3. ordered position $b\Delta e$;
4. exhaustive no-operation/matching-operation behavior;
5. shallow access to the residual continuation;
6. handler elimination replacing the designated layer rather than globally erasing an unordered row.

### Repair

It should not automatically preserve:

1. proof-irrelevant padding when insertion position is observable;
2. an unexplained $(-)^\sharp$ that changes effect order;
3. existence of a large end without size/continuity assumptions;
4. equations lacking naturality or coherence requirements;
5. any mismatch-forwarding behavior not stated operationally.

## 8. Recommended direction

Use the exact construction as a mathematical control case, but take optional layers as the intended main language:

$$
\widehat T_{b\Delta e}A
=
T_b\left(
\widehat T_eA+
\mathsf{Op}_\Delta(\widehat T_eA)
\right).
$$

Model padding initially by proof-relevant word embeddings, or choose an explicit canonical elaboration. Then derive the actual value-clause lifting from a fixed operational handler rule.

The next task should therefore not begin with the end formula in Remark 22. It should:

1. add $1\to\Delta$ to Stage 1 typing;
2. give operational rules for padded return, matching operation, and mismatching operation;
3. calculate examples with effects both before and after the optional layer;
4. derive the required semantic eliminator and its effect order;
5. compare the result back to `(Original-Value)` and `(Original-Op)`.

This follows the original philosophy without inheriting its unresolved assumptions.

