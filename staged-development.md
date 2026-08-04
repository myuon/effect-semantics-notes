# Staged development

研究対象を一度に定義せず、次の三段階を順に固定する。

## Stage 0 — Base-effect calculus

Current page: [Base calculus v1](base-calculus-v1.md)

含むもの:

- fine-grain CBV lambda calculus
- base operations
- base effect algebra $B$
- base-effect typing
- operational semantics

含まないもの:

- $\Delta$
- free operations
- handlers
- extended effects

Exit condition: syntax、typing、reductionを固定し、substitution、preservation、decompositionを紙上で確認する。

Stage 0のcurrent semantic candidateは [Base denotational semantics v1](base-denotational-semantics-v1.md) に置く。これはstrong graded monadでbase calculusだけを解釈し、free operationsやhandlersを含まない。

Substitution、preservation、request decomposition、determinism、internal reduction soundnessのpaper proofsは [Base metatheory v1](base-metatheory-v1.md) に置く。

Concrete Writer machineについては [Writer adequacy v1](writer-adequacy-v1.md) でtermination、evaluation soundness、ground adequacy、pure-grade reflection、sequential log law、contextual soundnessを検証する。これらを後のextension-preservation theoremのtest propertiesとする。

将来のrecursion追加に関するcategorical collapse constraintは [Fixpoint design constraints](fixpoint-design.md) に分離して記録する。Stage 0ではunrestricted pure fixpointを追加しない。

## Stage 1 — Add free operations

Stage 0へのconservative extensionとして、free interfaces $\Delta$ とsimple free-operation computationsだけを追加する。base calculusと同様、operation term自身はcontinuationを引数に取らない。

この段階で初めて検討するもの:

- base effectsとfree-operation effectsの合成
- free product $B*\mathcal D^*$ がtypingを正しく表すか
- `let` がfree operationを越えるpropagation
- operationを起こさないpathのeffect annotation

まだhandlerは追加しない。

Current candidate: [Free-operation extension v1](free-operation-extension-v1.md). Free tokens are exact, operations remain simple computations without continuation arguments, and Writer adequacy generalizes to finite free-interaction-tree adequacy.

Upper-bound alternative: [Optional free layers v1](optional-free-layers-v1.md) allows $1\to\Delta$, replaces exact operation nodes by skip-or-operation layers, and identifies proof-relevant padding coherence as the main additional requirement. This direction currently better matches the intended user-facing language.

The supplied thesis Definition 21 is analyzed in [Reading of the original design](original-design-reading.md). Its coercion $be\leq b\Delta e$ makes optional upper-bound layers part of the original philosophy, while its unexplained value-clause lifting and padding coherence remain to be repaired.

Concrete return/match/ignore/duplicate/mismatch tests are calculated in [Optional handler operational tests v1](optional-handler-tests-v1.md). They isolate the main fork between a conventional searching handler and the original positional layer eliminator.

The clarified source-level intention is reconstructed in [Intended shallow matcher v1](intended-shallow-matcher-v1.md): branches replace an operation result, the captured continuation resumes implicitly exactly once, and value/unmatched cases use an identity fallback that permanently ends the handler. This removes the arbitrary-return-clause, searching-forwarding, and continuation-usage assumptions from the core language.

The adopted Stage 2 source calculus and its provisional upper-bound typing are fixed in [Shallow matcher calculus v1](shallow-matcher-calculus-v1.md). Its operational rules are now stable; the representation of optional subeffect evidence remains a denotational design choice.

The first preservation proof is factored through typed residual contexts in [Residual context typing v1](residual-context-typing-v1.md). It establishes the matching order $e'e$ and shows that plain token elimination is restricted to exhaustive interface handlers; partial forwarding requires a trace-transforming effect type.

The core language therefore adopts exhaustive interface handlers: a handler indexed by $\Delta$ must provide one clause for every operation in $\Delta$. Partial operation matchers are deferred as a separate extension.

This choice is compared with Koka, Effekt, Frank, OCaml 5, and representative formal calculi in [Handler exhaustiveness survey](handler-exhaustiveness-survey.md). Typed interface-oriented languages support the exhaustive design, while OCaml illustrates dynamically partial forwarding without static effect safety.

Nested handlers and machine interaction are completed in [Stage 2 operational metatheory v1](stage2-operational-metatheory-v1.md). Its suspension semantics proves that base requests retain a pending matcher, while an unmatched free request removes it before an outer handler sees the request. This closes the remaining operational design gap.

The first Stage 3 denotational construction is [Shallow handler denotation v1](shallow-handler-denotation-v1.md). Assuming the optional-layer extended graded monad, it constructs the exhaustive shallow handler by coproduct case analysis, proves the skip and operation equations, and identifies construction of coherent optional weakening as the remaining global problem.

[Middle-padding obstruction v1](middle-padding-obstruction-v1.md) shows that proof-relevant word embeddings alone do not construct padding: inserting $\Delta$ between $b$ and $e$ requires a split $T_{be}\to T_bT_e$, opposite to graded multiplication. The representation theorem must therefore assume split structure, preserve syntactic segmentation, elaborate before flattening, or use a free interaction refinement.

[Writer representation comparison v1](writer-representation-comparison-v1.md) gives the decisive repeated-padding counterexample: a positional optional-layer eliminator distinguishes `op;skip` from `skip;op`, while the adopted source handler must inspect the same first actual operation in both cases. The main direction therefore moves to proof-irrelevant free interaction trees graded by trace upper bounds.

[Writer trace-graded trees v1](writer-trace-graded-trees-v1.md) carries out that construction. Downward-closed ordered trace languages form the grade quantale, finite Writer/free-operation trees form a graded monad, and the shallow handler has a monotone first-free-head grade transformer $\Phi_{\Delta,K}$.

[Writer tree metatheory v1](writer-tree-metatheory-v1.md) completes the paper-level concrete proof package: effect and reduction soundness, behavior-tree/request/ground adequacy, handler adequacy, Writer conservativity up to monad isomorphism, naturality, and a structural relation-lifting template.

[General base tree lifting v1](general-base-tree-lifting-v1.md) extracts the Writer-independent theorem. The free interaction tree, downset quantale, handler transformer, and structural liftings generalize to arbitrary typed algebraic base signatures. Writer's base isomorphism weakens in general to a typed fold into the chosen graded monad $T$.

[Free extension theorem v1](free-extension-theorem-v1.md) gives the detailed proof of the first main-theorem layer in `Set`: quantale laws, strong graded-monad laws, proof-irrelevant weakening, primitive operations, first-free-head handler grading and naturality, and the underlying free-monad universal property.

## Stage 2 — Add shallow handlers

Stage 1のcalculusにmatching shallow handlerを追加する。

この段階で初めて検討するもの:

- matching elimination
- base-operation forwarding
- mismatching free operation
- return clause
- shallow continuation
- handler output effects

## Stage 3 — Denotational reconstruction

Stages 0--2のoperational behaviorを固定した後、それを表現するdenotational semanticsを構成する。

ここで初めて比較するもの:

$$
X+\mathsf{Op}_\Delta(K(X))
$$

and

$$
K(X)+\mathsf{Op}_\Delta(K(X)).
$$

carrierを先に選び、syntaxやreductionをそれに合わせることはしない。
