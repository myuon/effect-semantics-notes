# Writer end-to-end certificate instance

## Status

**Concrete recursion-free derivation.**  This page instantiates the complete
chain

$$
\mathsf{BaseCert}
\Longrightarrow\mathsf{FreeCert}
\Longrightarrow\mathsf{TTCert}
\Longrightarrow\mathsf{ShallowCert}
$$

for ordered Writer effects and one free `ask` interface.

## 1. Base package

Let $W=\mathsf{Msg}^*$ and use the insertion preorder on words.  Put

$$
T_bA=\{(w,a)\mid w\preceq b\},
\qquad
\mathcal K=\mathsf{Id}.
$$

Return emits $\epsilon$, bind concatenates actual logs, and
$\mathsf{tell}_a(*)$ denotes $([a],*)$.  Weakening preserves $(w,a)$ and only
changes its proof that $w$ lies below the static bound.

The Writer machine and denotation satisfy `BaseCert`:

1. unique CBV position and deterministic typed response are immediate;
2. recursion-free normalization is the ordinary STLC reducibility argument;
3. log concatenation proves graded bind and weakening laws;
4. the invariant

   $$
   w_{\mathsf{acc}}\cdot
   \pi_1\llbracket M\rrbracket=w_{\mathsf{final}}
   $$

   proves response soundness and ground adequacy.

## 2. Indexed free carrier

Add

$$
\mathsf{ask}:\mathsf{String}\to\mathsf{Bool}
\quad\in\Delta.
$$

For Writer, the indexed layer specializes to

$$
(\mathcal H_A X)_d
=
\coprod_{b\in W}
T_b\left(
\coprod_{b\preceq d}A
+
\coprod_{\substack{e\\b\cdot\Delta\cdot e\le d}}
\mathsf{String}\times X_e^{\mathsf{Bool}}
\right).
$$

Finite syntax trees give its initial algebra directly.  Products with the
finite response type preserve the construction, so strength exists.  The
required base action sends $(w,t)\in T_b(\mathsf F_dA)$ to the tree obtained
by prefixing $w$ to the first Writer segment of $t$; associativity of word
concatenation gives

$$
\mathsf{baseAct}_{b,d}:T_b(\mathsf F_dA)
\to\mathsf F_{b\cdot d}A
$$

and its unit/multiplication laws.  This
discharges the indexed-initial-algebra premise of `Free-Transport` without an
ungraded approximation.

## 3. Operational and denotational calculation

Let

```text
M = tell_a;
    let x <- ask("continue?") in
    tell_b;
    return x
```

with bound

$$
[a]\cdot\Delta\cdot[b].
$$

Operationally, from the empty log it exposes

$$
\mathsf{askObs}\left(
\text{"continue?"},
\lambda r.([a,b],r)
\right),
$$

where $[a]$ has already been accumulated and the displayed continuation
records the additional $[b]$.

The indexed denotation is the same outer Writer segment, `ask` node and
response continuation.  Folding it into the canonical observation therefore
gives exactly the same observation.

## 4. Canonical TT pole

For every bound $e$, define

$$
C\mathrel{\mathcal O^W_e}t
\quad\Longleftrightarrow\quad
\mathsf{run}^\Delta(C)
=\mathsf{observe}^\Delta(t).
$$

The pole is weakening-coherent because weakening does not change the actual
log.  It is closed under:

- return, by equality of returned values and logs;
- `tell`, by prefixing both logs with the same message;
- `ask`, by equality of the tag/parameter and pointwise equality of the two
  Boolean continuations;
- bind, by associativity of word concatenation.

Hence the graded Writer `TTCert` follows.  The structural-to-TT inclusion is
an induction over finite Writer/free trees.  Constructor separation derives
reflection; no extended adequacy premise is used.

## 5. Affine shallow handler

Use

```text
return x        -> return x
ask(p, k)       -> k true
```

The response computation is pure, so $e'=1$.  `AffineCert` yields

$$
[a]\cdot\Delta\cdot[b]
\longmapsto
[a]\cdot1\cdot[b]=[a,b].
$$

Direct reduction gives

```text
tell_a; tell_b; return true
```

because the matching continuation is invoked once and the shallow handler is
not reinstalled.  Both operational and denotational observations are

$$
([a,b],\mathsf{true}).
$$

The operation clause is TT-compatible: pointwise-related continuations remain
related when both are applied to `true`.  Thus `ShallowCert` follows.

## 6. Certificate audit

| certificate condition | Writer witness |
|---|---|
| `BaseCert` response structure | `Id`; deterministic `tell` |
| branch normalization | recursion-free reducibility |
| indexed initial algebra | finite Writer/free trees |
| no-erasure | occurrence-preserving extended word preorder |
| `FreeCert` conservativity | old terms contain no `ask` node |
| structural graph law | induction over finite nodes |
| canonical pole closure | log concatenation and constructor congruence |
| `TTCert` | equality of Writer/free observations |
| `TTClause` | apply related continuations to the same `true` |
| `ShallowCert` adequacy | TT fundamental lemma plus constructor separation |

This is the first complete instance of the recursion-free main theorem.
