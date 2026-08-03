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

## Q-003: operational model \(S\) の正体

- syntax/tree monad
- evaluator induced monad
- transition system から得る resumption object
- term quotient

これにより \(S\) と \(T\) の間に morphism が自然か、relation のみが自然かが変わる。

## Q-004: extended effect words の代数

単なる交互列、free product、two-sorted word、normal form のどれが最も自然か。monoid structure と preorder の両立を先に証明する。

## Q-005: 必要な基礎圏の条件

最初は \(\mathbf{Set}\) で計算を確認し、その後に必要条件を抽出する案が有力。想定候補:

- finite products / coproducts
- exponentials または operation arity に対応する powers
- distributivity
- strong graded monad
- coproduct injection の分離性
- initial algebras（recursive construction を採る場合）

## Q-006: shallow と deep の境界

shallow handler では continuation を同じ handler で再処理しない。この一点が、finite structural extension と関係 lifting を可能にしているかを定理として抽出できるか。

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
