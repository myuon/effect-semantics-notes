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

を、ordered upper-bound effects、free operations、shallow handlers、fixpoints の順に拡張できるか。その拡張は、型付け、逐次合成、subeffecting、base conservativity、意味保存、観察可能性、adequacy、logical relations のどこまでを保存するか。

「任意の effect system」を無条件に一つの代数へ押し込めない。静的 grade、計算モデル、base primitives、観測、法則をまとめた **base semantic package** を入力とし、追加したい handler の強さごとに必要な仮定を特定する。

effect annotation は、runtimeで起きうるeffectsを順序を保って上から近似する静的情報として読む。一回の実行と完全一致する必要はない。deep handlerはprimitiveとして追加せず、standard shallow handlerとcomputation-level fixpointから導出する。

## 読み方

1. [Ordered-effect research program v5](research-program-v5.md) — 現在の前提と全体構成
2. [Functorial extension theorem](functorial-extension-theorem-v5.md) — 元の式 (2)--(4) への現在の主回答
3. [Graded TT-lifting](graded-tt-lifting-v5.md) — structural relation、観測関係、adequacy の接続
4. [Chapter I](chapter-1-foundations-v5.md) — 用語、基礎文法、base effect
5. [Chapter II](chapter-2-free-operations-v5.md) — ordered free-operation extension
6. [Chapter III](chapter-3-shallow-handlers-v5.md) — shallow handlerとeffect変換
7. [Chapter IV](chapter-4-fixpoint-derived-deep-v5.md) — fixpointとdeep handlerの導出
8. [Claims ledger](claims-ledger.md) — 既知・予想・未検証の台帳

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
