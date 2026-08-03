# Effect Semantics Research Notes

> This repository is rendered as a MyST website. Mathematical notation in the
> Markdown source is typeset in the browser, while the source remains easy to
> edit and review in Git.

一般の effect system に algebraic/free effects と shallow handlers を追加したとき、意味論・操作的意味論・両者の対応がどのように拡張されるかを調べるための研究ノート。

このノートは論文草稿ではない。定義、計算、仮説、失敗した案、反例、文献との対応を、確度を明示しながら蓄積する。

## 現在の問い

ベースの effect system に対して与えられた

- operational semantics
- denotational semantics
- 両者を結ぶ morphism / simulation / logical relation

を、free effect interface と shallow handler の追加に沿って一様に拡張できるか。その拡張は、型付け、逐次合成、subeffecting、意味保存、観察可能性、adequacy のどこまでを保存するか。

## 読み方

1. [Research map](research-map.md) — 問題全体と現在地
2. [Objects and notation](objects-and-notation.md) — 登場する対象と記法
3. [Baseline calculus v1](baseline-calculus-v1.md) — 以後の基準として固定する言語
4. [Minimal calculus v0](minimal-calculus-v0.md) — v1以前の探索記録
5. [Candidate constructions](candidate-constructions.md) — 構成案と計算
6. [Claims ledger](claims-ledger.md) — 既知・予想・未検証の台帳
7. [Open questions](open-questions.md) — 設計判断と未解決点
8. [Literature map](literature-map.md) — 関連研究を主張ごとに整理する場所
9. [Work log](work-log.md) — 議論と変更の履歴

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
