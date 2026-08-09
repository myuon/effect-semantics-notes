# Effect Semantics Research Notes

The published site includes both the mathematical research notes and an
[automatically generated Lean API reference](https://myuon.github.io/effect-semantics-notes/lean/).
The [Lean formalization index](lean-api-reference.md) maps the principal
mathematical results to their exact kernel-checked declarations.

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

最初に [Review guide and theorem dependency map](review-guide.md) を開く。
ここに標準的な読書順、各定義・定理の Lean 対応、形式化されていない
境界を集約している。

本文は次のように、具体的な計算から抽象定理へ進む。

1. [Chapter I: concrete base machines](chapter-1-operational-examples-v5.md)
2. [Chapter II: programs with free operations](chapter-2-operational-examples-v5.md)
3. [Writer](writer-end-to-end-v5.md)、[State](state-end-to-end-v5.md)、[Exception](exception-end-to-end-v5.md) の end-to-end instance
4. [Chapter III: shallow-handler calculations](chapter-3-operational-examples-v5.md)
5. [Chapter IV: recursive and derived-deep programs](chapter-4-operational-examples-v5.md)
6. [Language-level main theorem](language-graded-main-theorem-v6.md)
7. [Generic finite theorem](generic-free-extension-theorem-v1.md)
8. [Generic recursive theorem](generic-recursive-resumption-theorem-v1.md)
9. [Functorial extension theorem](functorial-extension-theorem-v5.md) と [package categories](package-categories-v5.md)

各 chapter では **operational examples → syntax/typing → denotation →
certificate → detailed proofs** の順に読む。旧 unordered 方針、探索メモ、
旧版は目次の後半に分離してあり、現在の主定理の依存関係には入らない。

## ステータス記法

査読用の正本ページでは、次の三区分を使う。

- **Lean checked**: 表示した API 宣言がその主張を kernel-check している
- **Paper abstraction**: 構成要素は形式化済みだが、その抽象的包装自体は紙上の記述
- **Boundary / conjecture**: 現在の定理としては主張しない

探索メモ内の旧ステータスは以下の意味を持つ。

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
