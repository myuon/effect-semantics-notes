# Exception end-to-end certificate instance

## Status

**Concrete recursion-free derivation.**  This instance checks abortive base
outcomes and confirms that free extension does not introduce a generic
`abort` constructor.

## 1. Base package

Use

$$
T_bA=A+\mathsf{Err},
\qquad\mathcal K=\mathsf{Id}.
$$

Bind propagates $\mathsf{inr}(e)$ without evaluating its continuation.
Observation separates return from error.  The ordinary short-circuit
equations establish `BaseCert`.

## 2. Free `ask` and base action

Add $\mathsf{ask}:1\to\mathsf{Bool}$ in $\Delta$.  The indexed finite carrier
has return, error and free-request boundaries.  Define

$$
\mathsf{act}_{b,d}:
\mathsf F_dA+\mathsf{Err}\to\mathsf F_{b\cdot d}A
$$

by embedding the contained tree on the left and producing a terminal error
layer on the right.  Exception short-circuiting proves the action laws.

## 3. Two scope calculations

The program

```text
raise_boom(*); ask(*)
```

terminates with `boom`; no `ask` node is constructed even though the upper
bound may contain

$$
\mathsf{raise}\cdot\Delta.
$$

Conversely,

```text
let x <- ask(*) in raise_boom(*)
```

first exposes `ask`, with a continuation that produces `boom` for either
Boolean response.  The indexed denotation has exactly these two shapes because
the outer Exception layer chooses error before entering any later free layer.

## 4. TT pole

Define the canonical pole by equality of the four separated observations:
return, error, free request, and its pointwise response continuations.  Return
and request closure are structural; error closure follows from

$$
\mathsf{inr}(e)\gg=k=\mathsf{inr}(e).
$$

This proves `TTCert`.  Constructor separation is particularly important here:
an error must not be identified with an unhandled free request.

## 5. Shallow handler

Use the affine handler

```text
return x   -> return x
ask(_, k)  -> k true
```

On `ask; raise_boom`, the handler handles the request once and its bare
continuation then raises `boom`.  Both semantics therefore observe the same
error.  On `raise_boom; ask`, the handler scrutinee reaches the terminal base
outcome before any free request; the error remains unchanged.

The effect transformation is sound:

$$
\Delta\cdot\mathsf{raise}
\longmapsto\mathsf{raise},
$$

while an earlier `raise` may prevent the optional request from occurring at
all.  Thus the complete recursion-free certificate chain also holds for
Exception.
