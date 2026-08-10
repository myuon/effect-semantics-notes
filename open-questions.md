# Open questions

## Q-001: 研究対象の calculus は何か

**Partially resolved.** Working calculus として Baseline v1 を採用した。元の修論の syntax、typing rules、operational observations の復元は、必須条件ではなく比較材料とする。

将来変更しうる点:

- call-by-value か CBPV か
- `val` と subsumption の規則
- handler の return/value clause の型
- continuation に残る tail effect
- handler が別 effect を発生できるか
- recursion、function types、effect polymorphism の有無

## Q-002: adequacy の観察は何か

候補:

1. return value の観察
2. return または未処理 operation という head form の観察
3. termination のみ
4. finite effect trace
5. contextual approximation/equivalence

**Working choice:** 最初の定理では return または未処理 operation という head form を観察する。強い観察は別 claim に分ける。

## Q-003: operational model $S$ の正体

- syntax/tree monad
- evaluator induced monad
- transition system から得る resumption object
- term quotient

これにより $S$ と $T$ の間に morphism が自然か、relation のみが自然かが変わる。

## Q-004: extended effect words の代数

単なる交互列、free product、two-sorted word、normal form のどれが最も自然か。monoid structure と preorder の両立を先に証明する。

## Q-005: 必要な基礎圏の条件

最初は $\mathbf{Set}$ で計算を確認し、その後に必要条件を抽出する案が有力。想定候補:

- finite products / coproducts
- exponentials または operation arity に対応する powers
- distributivity
- strong graded monad
- coproduct injection の分離性
- initial algebras（recursive construction を採る場合）

## Q-006: shallow と deep の境界

shallow handler では continuation を同じ handler で再処理しない。この一点が、finite structural extension と関係 lifting を可能にしているかを定理として抽出できるか。

**New deferred branch:** [Quantitative catch handlers — future direction](quantitative-catch-handlers-direction.md) proposes handler fuel $m\in\mathbb N_\infty$. Fuel $1$ searches through nonmatching interfaces and catches one matching occurrence; fuel $\omega$ is a candidate bridge to deep handling.

## Q-007: novelty

次のどの水準が既存で、どの組合せが未整理か。

- free/algebraic effect syntax
- shallow handler semantics
- graded/indexed semantics
- generic interpreter
- morphism lifting
- relational lifting
- adequacy preservation

新規性の判定は、数学を固定する前に断定しない。

## Q-008: head-normal handler か layer handler か

標準的 shallow handler は `return V` または最初の `op(V;k)` を観察する。一方 Candidate A は、指定された effect-word layer で `tail computation` または `op(V;k)` を観察する。

元の研究対象がどちらだったかを確定する。両方に意味がある場合は、別の構文操作として定義し、その間の対応定理を探す。

## Q-009: effect と head shape を分離すべきか

Baseline v1 の effect annotation は上界であり、handler が要求する head decomposition を保証しない。

比較対象:

- effect rows + forwarding
- sequential effect + separate head shape
- explicit layer type
- exact/canonical effect derivation

判定基準は、操作的 progress、意味論的 decomposition、subeffect coherence、元の modular-extension という目的の四点。

**Resolved for the main line:** 分離しない。exact typed free layerがheadとresidual continuationを直接保持する。head shapesはそのabstractionとしてのみ残す。

## Q-010: residual-aware shape は独立した型構造か

候補は

$$
X+\coprod_{\operatorname{op}:P\to R}
P\times(T_{e,s}X)^R.
$$

これは free shallow layer の carrier とほぼ同じ形をしている。次を判定する。

- syntax index として別に持つ必要があるか
- semantic free construction から inversion principle として導けるか
- operational model と denotational model の両方で同じ polynomial lifting を使えるか

**Current answer:** independent shapeではなくtyped free-layer polynomialとして扱う。

## Q-011: free-product normal formの粒度

$B*\mathcal D^*$ の標準的reduced wordは $B$ のnon-unit elementsと $\mathcal D^*$ のnonempty wordsを交互に持つ。個々の $\Delta$ を必ず一層として露出する場合、free-operation block内部をさらに分解して表記する必要がある。

決めること:

- consecutive free operation typesを一つのblockとして扱うか
- identity base segmentを挟んで一層ずつ扱うか
- handler eliminationがblockの先頭だけを除くか、typed block全体を扱うか

## Q-012: free-layerのreturn branch

候補:

$$
X+\mathsf{Op}_\Delta(K)
$$

または

$$
K+\mathsf{Op}_\Delta(K).
$$

前者はstandard shallow return clause、後者はlayer skip/tail preservationに対応する。元のtyping ruleとbindを再構成して決める。

## Q-013: external-root carrierはいつ標準FreeTを表示するか

主定理では[strong graded FreeTの存在](graded-freet-existence-v1.md)を仮定し、
`baseAct`をそのfold/unfold構造から導出する。したがって標準FreeTについて
`baseAct`を独立な追加構造とする問題は解消した。

残る問題は、grade-root coproductを外側に出した別のindexed carrierが、いつ
標準FreeTと同型になるかである。coherentなroot exposureはその十分条件を与えるが、
State、Exception、finite SubDistなどでは一般に成り立たない。この失敗はFreeT
そのものの不存在を意味せず、外部root表示が使えないことだけを意味する。
