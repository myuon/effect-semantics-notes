# Common chapter method v5

## Status

**Adopted development protocol.**  Every chapter follows the same six-stage
cycle.  A chapter is not considered complete merely because its syntax or
semantic carrier has been proposed.

## The six stages

### 1. Fix syntax and typing

State the new terms, values, evaluation contexts and typing rules.  Effects are
ordered upper approximations; specify their preorder, branch weakening and
sequencing.

### 2. Write the operational semantics

Give direct CBV rules, terminal/request forms and unique decomposition of the
next evaluation position.  Any
metatheoretic continuation must be distinguished from source syntax.

### 3. Calculate concrete systems

Run closed programs in Writer, State and Exception machines.  These examples
must include sequencing, branching and an interaction that would be wrong if
effect order were forgotten.

### 4. Define denotational semantics

Interpret every typing rule.  Identify the precise extra structure required
from the preceding chapter; do not hide it behind the word “monad.”

### 5. Prove local metatheory

At minimum: substitution, preservation, effect-aware progress/decomposition,
operational soundness, and the declared adequacy statement.  With recursion,
normalization is replaced by an explicit partiality or fixed-point principle.

### 6. Extract a structure-preservation certificate

Package exactly what the next chapter may reuse.  The certificate lists both
positive fields and boundaries.  A later chapter proves a transformer

$$
\mathsf{Cert}_n(P)
\longrightarrow
\mathsf{Cert}_{n+1}(\mathsf{Ext}_{n+1}P),
$$

not an unqualified claim that “all good properties are preserved.”

## Chapter dependencies

```{mermaid}
flowchart LR
  C1["Chapter I: BaseCert"] --> C2["Chapter II: FreeCert"]
  C2 --> C3["Chapter III: ShallowCert"]
  C3 --> C4["Chapter IV: RecursiveCert"]
  C4 --> D["Derived deep-handler theorem"]
```

## Required concrete checkpoints

Each chapter uses the same bases for comparability.

| base | observation | order-sensitive checkpoint |
|---|---|---|
| Writer | returned value and emitted word | `tell "a"; tell "b"` differs from the reverse order |
| State | returned value and final store | the bounds `read·write` and `write·read` remain distinct |
| Exception | return or first raised exception | an early throw prevents later possible effects from running |

The examples are not proofs of the generic theorem.  They are model checks
that reveal missing hypotheses before abstraction.
