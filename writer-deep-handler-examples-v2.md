# Writer deep-handler examples v2

## Status

**Operational calculations for validating the common calculus.** No general
theorem is claimed on this page.

## 1. Writer instance

Let $(W,\cdot,\epsilon)$ be the free monoid of output letters.  Configurations
are

$$
\langle w,M\rangle.
$$

The base primitive is

$$
\operatorname{tell}(a):1
$$

with transition

$$
\langle w,\operatorname{tell}(a)\rangle
\longrightarrow
\langle w\cdot a,\operatorname{return}()\rangle.
\tag{W-Tell}
$$

All ordinary term reductions leave $w$ unchanged, and evaluation contexts lift
the Writer transition.

Use two free interfaces:

$$
\mathsf{Ask}=\{\operatorname{ask}:1\to\mathsf{Bool}\},
$$

$$
\mathsf{Ping}=\{\operatorname{ping}:1\to1\}.
$$

Define linear deep handlers

$$
\begin{aligned}
h_{\mathsf{Ask}}^v=\{&
\operatorname{return}(x)\mapsto\operatorname{return}x;\\
&\operatorname{ask}(u,k)\mapsto k\,v
\},
\end{aligned}
$$

and

$$
\begin{aligned}
h_{\mathsf{Ping}}=\{&
\operatorname{return}(x)\mapsto\operatorname{return}x;\\
&\operatorname{ping}(u,k)\mapsto k\,()
\}.
\end{aligned}
$$

Write $H_A^v(M)$ and $H_P(M)$ for the corresponding handled terms.

## 2. Conditional request versus return

Consider

$$
M_b=H_A^{\mathsf{true}}(
\mathbf{if}\ b\ \mathbf{then}\operatorname{ask}()
\ \mathbf{else}\operatorname{return}\mathsf{false}).
$$

Its free row before handling is $\{\mathsf{Ask}\}$ and after handling is empty.

For $b=\mathsf{false}$:

$$
\begin{aligned}
\langle\epsilon,M_{\mathsf{false}}\rangle
&\longrightarrow
\langle\epsilon,H_A^{\mathsf{true}}(
\operatorname{return}\mathsf{false})\rangle\\
&\longrightarrow
\langle\epsilon,\operatorname{return}\mathsf{false}\rangle.
\end{aligned}
$$

No operation is caught, yet $\mathsf{Ask}$ is correctly absent from the
outward row.

For $b=\mathsf{true}$:

$$
\begin{aligned}
\langle\epsilon,M_{\mathsf{true}}\rangle
&\longrightarrow
\langle\epsilon,H_A^{\mathsf{true}}(\operatorname{ask}())\rangle\\
&\longrightarrow
\langle\epsilon,H_A^{\mathsf{true}}(
\operatorname{return}\mathsf{true})\rangle\\
&\longrightarrow
\langle\epsilon,\operatorname{return}\mathsf{true}\rangle.
\end{aligned}
$$

This confirms that row elimination means absence of an escaping request, not
guaranteed handler invocation.

## 3. Forwarding before a matching request

Consider

$$
M=H_P\left(
H_A^{\mathsf{true}}\left(
\mathbf{let}\ u\leftarrow\operatorname{ping}()\ \mathbf{in}\
\operatorname{ask}()
\right)
\right).
$$

The inner $\mathsf{Ask}$ handler does not match $\operatorname{ping}$.  The
outer $\mathsf{Ping}$ handler sees the request through the transparent context

$$
E^{\mathsf{Ping}}=
H_A^{\mathsf{true}}(
\mathbf{let}\ u\leftarrow[]\ \mathbf{in}\operatorname{ask}()).
$$

Its resumption is

$$
\lambda y.
H_P\left(
H_A^{\mathsf{true}}(
\mathbf{let}\ u\leftarrow\operatorname{return}y\ \mathbf{in}\
\operatorname{ask}())
\right).
$$

After $h_{\mathsf{Ping}}$ resumes with $()$, reduction continues under the
pending Ask handler:

$$
\begin{aligned}
M
&\longrightarrow^*
H_P(H_A^{\mathsf{true}}(\operatorname{ask}()))\\
&\longrightarrow^*
\operatorname{return}\mathsf{true}.
\end{aligned}
$$

Thus a nonmatching request is forwarded without ending the inner handler.

## 4. Two matching requests

Let

$$
M=H_A^{\mathsf{true}}\left(
\mathbf{let}\ x\leftarrow\operatorname{ask}()\ \mathbf{in}\
\mathbf{let}\ y\leftarrow\operatorname{ask}()\ \mathbf{in}\
\operatorname{return}y
\right).
$$

The first matching rule supplies the deep resumption

$$
k_1=\lambda z.H_A^{\mathsf{true}}\left(
\mathbf{let}\ x\leftarrow\operatorname{return}z\ \mathbf{in}\
\mathbf{let}\ y\leftarrow\operatorname{ask}()\ \mathbf{in}\
\operatorname{return}y
\right).
$$

The clause invokes $k_1\,\mathsf{true}$, so the second request remains under
the same handler.  Hence

$$
M\longrightarrow^*\operatorname{return}\mathsf{true}.
$$

A shallow resumption would leave the second $\mathsf{Ask}$ request unhandled.

## 5. Handler clause with a Writer effect

Define

$$
\begin{aligned}
h_A^a=\{&
\operatorname{return}(x)\mapsto\operatorname{return}x;\\
&\operatorname{ask}(u,k)\mapsto
\mathbf{let}\ z\leftarrow\operatorname{tell}(a)\ \mathbf{in}\
k\,\mathsf{true}
\}.
\end{aligned}
$$

Apply it to two requests:

$$
M=H_A^a\left(
\mathbf{let}\ x\leftarrow\operatorname{ask}()\ \mathbf{in}\
\mathbf{let}\ y\leftarrow\operatorname{ask}()\ \mathbf{in}\
\operatorname{return}()
\right).
$$

The first clause emits $a$ and resumes under the handler; the second clause
emits another $a$.  Therefore

$$
\langle\epsilon,M\rangle
\longrightarrow^*
\langle aa,\operatorname{return}()\rangle.
$$

By contrast,

$$
H_A^a(\operatorname{return}())
$$

produces $\epsilon$, and a program with one request produces $a$.  All three
inputs may be typed with the same free-row upper bound $\{\mathsf{Ask}\}$.

This is the concrete precision obstruction:

$$
\{\mathsf{Ask}\}
$$

does not determine whether the handler inserts $\epsilon$, $a$, or $aa$ into
the Writer trace.

## 6. Nested handlers for distinct interfaces

Define effectful clauses that log their interface:

$$
\operatorname{ask}(u,k)\mapsto
\operatorname{tell}(a);k\,\mathsf{true},
$$

$$
\operatorname{ping}(u,k)\mapsto
\operatorname{tell}(p);k\,().
$$

Here the semicolon abbreviates ordinary fine-grain sequencing with `let`.
Write the resulting handlers as $H_A^a$ and $H_P^p$.

For

$$
N=
\mathbf{let}\ u\leftarrow\operatorname{ping}()\ \mathbf{in}\
\mathbf{let}\ x\leftarrow\operatorname{ask}()\ \mathbf{in}\
\operatorname{return}(),
$$

both nestings

$$
H_P^p(H_A^a(N))
\qquad\text{and}\qquad
H_A^a(H_P^p(N))
$$

produce the Writer word $pa$ under these linear clauses.  Forwarding preserves
the operational request order.

This example does **not** establish handler commutativity.  Clauses that emit
the other interface, discard a continuation, or resume it multiple times can
distinguish the nesting order.  It only checks that ordinary forwarding does
not reorder the two original requests.

## 7. Base-only program under a handler

Let

$$
M=H_A^{\mathsf{true}}\left(
\mathbf{let}\ u\leftarrow\operatorname{tell}(w)\ \mathbf{in}\
\operatorname{return}()
\right).
$$

The Writer transition occurs inside the handled computation:

$$
\begin{aligned}
\langle\epsilon,M\rangle
&\longrightarrow
\langle w,H_A^{\mathsf{true}}(
\mathbf{let}\ u\leftarrow\operatorname{return}()\ \mathbf{in}\
\operatorname{return}())\rangle\\
&\longrightarrow^*
\langle w,\operatorname{return}()\rangle.
\end{aligned}
$$

The free handler is operationally inert with respect to a base-only Writer
program, apart from structural traversal.

## 8. Findings from the calculations

The proposed common semantics passes the first operational checks.

1. Conditional may-effects need no type-level operation/return sum.
2. Nonmatching forwarding retains pending handlers.
3. Deep reinstallation catches successive matching requests.
4. Base-only execution is unchanged.
5. An unordered free row is sufficient for outward $\Delta$ elimination.
6. The same row is insufficient to calculate effects inserted by an
   effectful clause into a noncommutative Writer trace.

The sixth finding is not a failure of free-effect safety.  It separates two
questions:

$$
\text{Does }\Delta\text{ escape?}
$$

and

$$
\text{What base behavior is induced by interpreting all }\Delta\text{ nodes?}
$$

The unordered row answers the first and intentionally forgets information
needed by the second.

## 9. Next obligations for Writer

- formalize request decomposition with $\Delta$-transparent contexts;
- prove determinism of the direct reduction relation;
- prove free-row preservation;
- define the Writer-plus-free interaction tree;
- define its fold into $A\times W$ after handling;
- prove operational/denotational agreement for the six examples;
- formulate the minimal counterexample to a principal Writer-grade transformer.

The first three obligations, together with empty-row safety, deep elimination,
and qualified base conservativity, are discharged in [Writer operational
metatheory v2](writer-operational-metatheory-v2.md).
