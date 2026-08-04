# Effect Semantics Research Notes

> This repository is rendered as a MyST website. Mathematical notation in the
> Markdown source is typeset in the browser, while the source remains easy to
> edit and review in Git.

既存の effectful language に user-defined free operations と handlers を後付けするとき、どの構造が必要で、意味論・操作的意味論・両者の対応をどこまで保存できるかを調べるための研究ノート。

このノートは論文草稿ではない。定義、計算、仮説、失敗した案、反例、文献との対応を、確度を明示しながら蓄積する。

## 現在の問い

中心の問いは次である。

> **What structure makes an effectful language extensible by user-defined operations and handlers?**

ベース言語に対して与えられた

- operational semantics
- denotational semantics
- 両者を結ぶ morphism / simulation / logical relation

を、unordered free-effect rows と標準的な deep handlers の追加に沿って拡張できるか。その拡張は、型付け、逐次合成、subeffecting、base conservativity、意味保存、観察可能性、adequacy、logical relations のどこまでを保存するか。

「任意の effect system」を無条件に一つの代数へ押し込めない。静的 grade、計算モデル、base primitives、観測、法則をまとめた **base semantic package** を入力とし、追加したい handler の強さごとに必要な仮定を特定する。

以前の ordered trace と first-head shallow handler の開発は破棄しない。これは、順序を追う refinement がなぜ難しいか、unordered abstraction が何を忘れるかを示す比較対象として保存する。

## 読み方

1. [Research map](research-map.md) — 新旧の研究線と現在地
2. [Extensibility question v2](extensibility-question-v2.md) — 新しい中心問いと主張候補
3. [Base semantic package v2](base-semantic-package-v2.md) — 拡張の入力として何を固定するか
4. [Extension audit v2](extension-audit-v2.md) — 保存性と必要仮定の検査表
5. [Unordered/deep baseline v2](unordered-deep-baseline-v2.md) — 既知の基準言語
6. [Concrete base program v2](concrete-base-program-v2.md) — 具体例から一般化する開発順序
7. [Novelty map v2](novelty-map-v2.md) — 先行研究との重なりと新規性候補
8. [Research synthesis v1](research-synthesis-v1.md) — 以前のordered/shallow探索の到達点
9. [Claims ledger](claims-ledger.md) — 既知・予想・未検証の台帳
10. [Open questions](open-questions.md) — 設計判断と未解決点
11. [Literature map](literature-map.md) — 関連研究

## ステータス記法

- **Established**: 定義または証明を手元で確認済み
- **Derived**: 明示した仮定から紙上で導出済み
- **Conjecture**: 成立を予想するが証明未了
- **Candidate**: 複数案の一つで、採用未決定
- **Question**: 問い自体が未整理
- **Rejected**: 反例または目的との不一致により不採用

「文献にある」と「この設定で証明できた」を混同しない。前者は Literature、後者は Claims ledger に記録する。

## Editing and publishing

The notes use [MyST Markdown](https://mystmd.org/) and its book-style website.
See [CONTRIBUTING.md](CONTRIBUTING.md) for local preview and editing rules.
Pushing `main` triggers the GitHub Pages workflow in
`.github/workflows/pages.yml`.
