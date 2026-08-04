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

## Stage 1 — Add free operations

Stage 0へのconservative extensionとして、free interfaces $\Delta$ とfree operation nodesだけを追加する。

この段階で初めて検討するもの:

- base effectsとfree-operation effectsの合成
- free product $B*\mathcal D^*$ がtypingを正しく表すか
- `let` がfree operationを越えるpropagation
- operationを起こさないpathのeffect annotation

まだhandlerは追加しない。

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

