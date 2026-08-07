# Chapter I — operational semantics and concrete machines

## Status

**Derived operational development.**  This page expands the syntax fixed in
[Chapter I](chapter-1-foundations-v5.md).  There are still no free operations,
handlers or fixed points.

## 1. Evaluation contexts and internal reduction

Because values are syntactically separated from computations, the only
computation position evaluated under sequencing is

$$
\mathcal E::=[-]
\mid
\mathbf{let}\ x\leftarrow\mathcal E\ \mathbf{in}\ N.
$$

The principal internal reductions are

$$
(\lambda x.M)V\longrightarrow M[V/x],
\tag{B-$\beta$}
$$

$$
\mathbf{let}\ x\leftarrow\mathsf{return}\,V\ \mathbf{in}\ N
\longrightarrow N[V/x],
\tag{B-Let}
$$

$$
\mathbf{if}\ \mathsf{true}\ \mathbf{then}\ M\ \mathbf{else}\ N
\longrightarrow M,
$$

$$
\mathbf{if}\ \mathsf{false}\ \mathbf{then}\ M\ \mathbf{else}\ N
\longrightarrow N,
$$

with the analogous two rules for sum elimination.  Reduction is closed under
$\mathcal E$.

A base primitive does not reduce internally.  The exposed form is

$$
\mathcal E[\beta(V)].
$$

The selected base machine observes the request, updates its machine state, and
returns a value at the same hole.  No continuation is a syntactic argument of
$\beta$.

## 2. Generic decomposition

For a closed well-typed computation, exactly one of the following holds:

1. it is $\mathsf{return}\,V$;
2. it has a unique internal reduct;
3. it decomposes uniquely as $\mathcal E[\beta(V)]$.

The proof is by induction on the computation syntax, using canonical forms for
functions, booleans, products and sums.  In a `let`, either the left computation
reduces, returns, or exposes its unique request; each case determines the
enclosing behavior uniquely.

## 3. Writer instance

Let messages range over an alphabet $\mathsf{Msg}$.  Use exact grades

$$
B_W=\mathsf{Msg}^*,
$$

with concatenation and empty word $\epsilon$.  The primitive family is

$$
\mathsf{tell}_a:1\to1,
\qquad
|\mathsf{tell}_a|=[a].
$$

A configuration is $\langle M,w\rangle$.  The external rule is

$$
\langle\mathcal E[\mathsf{tell}_a(*)],w\rangle
\longrightarrow_W
\langle\mathcal E[\mathsf{return}\,*],w\cdot[a]\rangle.
\tag{W-Tell}
$$

Consider

```text
let _ <- tell_a(*) in
let _ <- tell_b(*) in
return true
```

Its machine run is

$$
\begin{aligned}
\langle M,\epsilon\rangle
&\longrightarrow_W
\langle\mathbf{let}\ \_\leftarrow\mathsf{return}\,*\ \mathbf{in}
       \mathbf{let}\ \_\leftarrow\mathsf{tell}_b(*)\ \mathbf{in}
       \mathsf{return}\,\mathsf{true},[a]\rangle\\
&\longrightarrow_W^*
\langle\mathsf{return}\,\mathsf{true},[a,b]\rangle.
\end{aligned}
$$

Its exact behavior is $([a,b],\checkmark)$.  Reversing the two source statements
produces $[b,a]$, so a commutative effect abstraction would lose an observable
fact.

### Conditional Writer language

For

```text
if c then tell_a(*) else return *
```

the static behavior language is

$$
\{([a],\checkmark),(\epsilon,\checkmark)\}.
$$

At runtime exactly one word is produced.  This is the basic distinction between
an actual trace and a static trace language.

## 4. State instance

Let the store be Boolean and use

$$
\mathsf{get}:1\to\mathsf{Bool},
\qquad
\mathsf{put}:\mathsf{Bool}\to1.
$$

Runtime events retain values:

$$
\mathsf{get}(s),
\qquad
\mathsf{put}(s').
$$

Configurations are triples $\langle M,s,t\rangle$, where $t$ is the accumulated
event trace:

$$
\langle\mathcal E[\mathsf{get}(*)],s,t\rangle
\longrightarrow_S
\langle\mathcal E[\mathsf{return}\,s],s,
t\cdot[\mathsf{get}(s)]\rangle,
$$

$$
\langle\mathcal E[\mathsf{put}(s')],s,t\rangle
\longrightarrow_S
\langle\mathcal E[\mathsf{return}\,*],s',
t\cdot[\mathsf{put}(s')]\rangle.
$$

Run

```text
let x <- get(*) in
let _ <- put(not x) in
return x
```

from `true`.  It yields

$$
\langle\mathsf{return}\,\mathsf{true},
\mathsf{false},
[\mathsf{get}(\mathsf{true}),\mathsf{put}(\mathsf{false})]\rangle.
$$

From `false`, it yields the corresponding trace

$$
[\mathsf{get}(\mathsf{false}),\mathsf{put}(\mathsf{true})].
$$

The static annotation may abstract both to the language described by the
pattern $\mathsf{get}\cdot\mathsf{put}$, while the denotation retains the
value-dependent trace.

## 5. Exception instance

Fix a set $\mathsf{Err}$ and primitives

$$
\mathsf{raise}_e:1\to A
$$

for every result type $A$.  A terminal machine outcome is
$\mathsf{error}(e,t)$, where $t$ records events preceding the exception:

$$
\langle\mathcal E[\mathsf{raise}_e(*)],t\rangle
\longrightarrow_X
\mathsf{error}(e,t\cdot[\mathsf{raise}(e)]).
\tag{X-Raise}
$$

Thus

```text
let _ <- raise_boom(*) in
tell_a(*)
```

terminates at `error(boom,[raise(boom)])`; the later Writer event is never
reached.  Conversely,

```text
let _ <- tell_a(*) in
raise_boom(*)
```

has observable behavior

$$
([\mathsf{tell}(a),\mathsf{raise}(\mathsf{boom})],
\mathsf{abort}(\mathsf{boom})).
$$

The completion-sensitive product validates

$$
([\mathsf{raise}(\mathsf{boom})],\mathsf{abort}(\mathsf{boom}))
\mathbin{;}L
=
([\mathsf{raise}(\mathsf{boom})],\mathsf{abort}(\mathsf{boom}))
$$

for every possible tail language $L$.

This combined example will later check that free-operation handlers preserve
the base prefix before a handled request.

## 6. Operational conclusions

All three machines are deterministic.  In the recursion-free calculus every
primitive either returns a response or produces a classified terminal outcome,
so the standard reducibility argument gives normalization to a unique machine
observation.  These facts become fields of the Chapter-I certificate rather
than implicit global assumptions.
