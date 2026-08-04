# Writer representation comparison v1

## Status

**Decisive concrete comparison: free interaction trees match the adopted operational handler; positional optional layers do not without further search/quotient structure.**

We compare two denotational presentations over the concrete Writer base model:

1. segmented optional layers;
2. a free finite interaction tree with explicit Writer and free-operation nodes.

The comparison reveals that the previously proposed one-layer algebra describes
a positional layer eliminator, not yet the adopted “inspect the first actual
free request” handler.

## 1. Concrete Writer base

Let

$$
T_1X=X,
\qquad
T_wX=\mathsf{List}(\mathsf{String})\times X,
$$

with

$$
1\leq w,
\qquad
w\cdot w=w.
$$

Graded multiplication at $w,w$ concatenates logs:

$$
\mu_{w,w}
(\ell_1,(\ell_2,x))
=
(\ell_1\mathbin{++}\ell_2,x).
$$

There is no distinguished inverse split. For every cut
$\ell=\ell_1\mathbin{++}\ell_2$,

$$
(\ell,x)
\longmapsto
(\ell_1,(\ell_2,x))
$$

is a section at that element. In particular,

$$
\delta_L(\ell,x)=([],(\ell,x))
$$

and

$$
\delta_R(\ell,x)=(\ell,([],x))
$$

both flatten back to $(\ell,x)$. Neither is selected by the Writer monad laws.

## 2. Segmented optional-layer representation

For one interface token, the proposed carrier is

$$
S_{w\Delta w}X
=
\mathsf{List}(\mathsf{String})
\times
\left(
  T_wX+
  \mathsf{Op}_\Delta(T_wX)
\right).
$$

An element records:

- a Writer prefix before the selected $\Delta$ boundary;
- either a skipped boundary with a Writer tail;
- or an actual $\Delta$ request with Writer continuations.

For the no-operation program

```text
tell("a");
tell("b");
return false
```

all of the following segmentations flatten to the same Writer result:

$$
([],\mathsf{inl}([\text{"a"},\text{"b"}],\mathsf{false})),
$$

$$
([\text{"a"}],\mathsf{inl}([\text{"b"}],\mathsf{false})),
$$

$$
([\text{"a"},\text{"b"}],\mathsf{inl}([],\mathsf{false})).
$$

Thus middle padding amounts concretely to choosing a cut in the log.

## 3. Free Writer interaction tree

Define finite trees by

$$
\begin{aligned}
\mathsf{Tree}(X)::={}&
\mathsf{ret}(x)\\
&\mid\mathsf{tell}(s,t)\\
&\mid\mathsf{op}_\Gamma(p,k),
\end{aligned}
$$

where for
$\operatorname{op}:P\to R\in\Gamma$,

$$
p:P,
\qquad
k:R\to\mathsf{Tree}(X).
$$

Tree bind is structural:

$$
\mathsf{ret}(x)\mathbin{\mathsf{bind}}f=f(x),
$$

$$
\mathsf{tell}(s,t)\mathbin{\mathsf{bind}}f
=
\mathsf{tell}(s,t\mathbin{\mathsf{bind}}f),
$$

$$
\mathsf{op}_\Gamma(p,k)\mathbin{\mathsf{bind}}f
=
\mathsf{op}_\Gamma
(p,\lambda r.k(r)\mathbin{\mathsf{bind}}f).
$$

No padding node occurs. Static upper bounds do not become runtime data.

The base-only observation map

$$
\mathsf{run}_W:
\mathsf{Tree}_{\mathrm{base}}(X)
\to
\mathsf{List}(\mathsf{String})\times X
$$

collects `tell` nodes in order. It is a monad morphism on the base-only
fragment.

## 4. The operational handler on trees

Let $c_{\operatorname{op}}:P\to\mathsf{Tree}(R)$ be exhaustive clauses for
$\Delta$. Define the one-shot handler by recursion only through **base** nodes:

$$
\mathsf{handle}_\Delta(\mathsf{ret}(x))
=
\mathsf{ret}(x),
\tag{TW-Ret}
$$

$$
\mathsf{handle}_\Delta(\mathsf{tell}(s,t))
=
\mathsf{tell}(s,\mathsf{handle}_\Delta(t)),
\tag{TW-Tell}
$$

$$
\mathsf{handle}_\Delta
(\mathsf{op}_\Delta(p,k))
=
c_{\operatorname{op}}(p)
\mathbin{\mathsf{bind}}
k,
\tag{TW-Match}
$$

and, for $\Gamma\neq\Delta$,

$$
\mathsf{handle}_\Delta
(\mathsf{op}_\Gamma(p,k))
=
\mathsf{op}_\Gamma(p,k).
\tag{TW-Other}
$$

There is no recursive handler occurrence in `TW-Match` or `TW-Other`.

This exactly mirrors the direct semantics:

- execute Writer/base work while searching;
- stop at the first actual free request;
- handle it if its interface is $\Delta$;
- otherwise forward it;
- in either free-request case, never reinstall the handler.

## 5. Basic calculations

Let

$$
c_{\mathsf{choose}}(*)
=
\mathsf{tell}(\text{"op"},\mathsf{ret}(\mathsf{true})).
$$

### Matching request

The program

```text
tell("before");
x <- choose_Delta(*);
tell("after");
return x
```

denotes

$$
\mathsf{tell}
(\text{"before"},
  \mathsf{choose}_\Delta
  (*,\lambda x.
    \mathsf{tell}(\text{"after"},\mathsf{ret}(x)))).
$$

Handling gives

$$
\mathsf{tell}
(\text{"before"},
  \mathsf{tell}
  (\text{"op"},
    \mathsf{tell}(\text{"after"},\mathsf{ret}(\mathsf{true})))).
$$

Writer observation is

$$
([\text{"before"},\text{"op"},\text{"after"}],\mathsf{true}).
$$

### No free request

For

$$
\mathsf{tell}(\text{"a"},
  \mathsf{tell}(\text{"b"},\mathsf{ret}(\mathsf{false}))),
$$

`TW-Tell` reaches `TW-Ret`, so the tree is unchanged. All possible segmented
cuts from Section 2 flatten to this same result.

### Other interface first

For

$$
\mathsf{ask}_\Gamma
(*,\lambda z.\mathsf{choose}_\Delta(*,k_z)),
$$

`TW-Other` returns the entire tree unchanged. In particular, it does not recurse
into the continuation to find the later `choose`.

## 6. The decisive repeated-padding test

Give a program with one actual `choose` the upper bound

$$
\Delta\Delta.
$$

A proof-relevant segmented presentation has two embeddings:

$$
\mathsf{op};\mathsf{skip}
$$

and

$$
\mathsf{skip};\mathsf{op}.
$$

Suppose a positional one-layer algebra handles only the first represented
layer.

- On `op;skip`, it sees and handles `choose`.
- On `skip;op`, its skip case returns the tail unchanged, so `choose` remains.

The two padding derivations become operationally distinguishable.

But the adopted source handler does not inspect typing evidence or silent
padding. It evaluates to the first **actual** free request. Both derivations
describe the same runtime tree

$$
\mathsf{choose}_\Delta(*,k),
$$

and both must therefore be handled identically by `TW-Match`.

This is a counterexample to using the simple local skip algebra

$$
h(\mathsf{inl}(z))=z
$$

as the denotation of the adopted source handler when $z$ may contain later free
layers.

## 7. Skip is not final return — again

The earlier distinction is now operationally decisive:

- `skip` means only that one **static optional boundary** was unused;
- `ret` means that the **whole dynamic computation** returned a value.

Our source handler ends on `ret`, not on a static `skip`. Therefore a semantics
that represents padding explicitly must either:

1. make the handler traverse skip evidence until it reaches a dynamic head;
2. quotient/erase skips before handling;
3. avoid representing skips as runtime tree nodes.

The one-layer algebra in
[Shallow handler denotation v1](shallow-handler-denotation-v1.md) chose none of
these and is therefore a positional eliminator rather than the adopted source
handler.

## 8. Comparison result

| Criterion | Segmented optional layers | Free Writer interaction tree |
|---|---|---|
| Writer order | explicit by segment | explicit by `tell` nodes |
| actual free request | stored at selected layer | stored as operation node |
| silent padding | semantic `skip` data | absent |
| repeated-padding proof irrelevance | fails for positional eliminator | automatic |
| first actual free-head matching | requires skip traversal/quotient | direct structural recursion |
| shallow continuation | possible | direct: do not recurse into $k$ |
| map to ordinary Writer | flatten segments | run base-only tree |
| arbitrary base monad reuse | needs semantic split at insertion | base model becomes an interpretation target |

## 9. Revised conclusion

For the operational language we fixed, the free interaction presentation is the
better reference semantics.

The segmented construction remains useful for a different construct:

> eliminate a statically selected effect boundary.

That construct resembles the literal positional reading of the original
$\widehat T_{b\Delta e}$ formula, but it is not the current first-actual-head
handler unless additional skip-search coherence is supplied.

The most promising main direction is therefore:

1. define a free finite interaction semantics with base and free nodes;
2. grade trees by proof-irrelevant ordered trace upper bounds;
3. interpret base-only trees into $T$;
4. define the shallow handler structurally as in Section 4;
5. prove operational adequacy in Writer first;
6. formulate preservation of base interpretations as a refinement/morphism
   theorem rather than carrier equality.

This changes the expected main result from a strict carrier extension toward an
adequacy-preserving free refinement, unless stronger splitting assumptions are
explicitly imposed on $T$.
