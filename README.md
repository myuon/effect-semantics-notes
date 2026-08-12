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

公開ノートは内容の役割に従って5部に分けている。

1. [Motivation and examples](motivation-and-examples.md): 何が起きるかを具体的なプログラムで見る。
2. [Formal setting and definitions](formal-setting-and-definitions.md): 構文、判断、意味論的対象を固定する。
3. [Theorem statements](theorem-statements.md): concreteな章からabstract transport theoremへ進む。
4. [Proofs and dependencies](proofs-and-dependencies.md): 詳細証明と横断的な証明依存を確認する。
5. [Scope, status, and open obligations](scope-and-open-obligations.md): conditionalな主張、未解決事項、形式化状況を確認する。

定義や定理に付いた **Lean** リンクはstatementの近くに置く。リンク先は
対応するkernel-checked declarationであり、単なる関連ファイルではない。

全statementの対応表が必要な場合は [Review guide and theorem dependency
map](review-guide.md) を参照する。

本文は次のように、具体的な計算から抽象定理へ進む。

1. [Chapter I: concrete base languages](chapter-1-overview-v5.md)
2. [Chapter II: programs with free operations](chapter-2-operational-examples-v5.md)
3. [Writer](writer-end-to-end-v5.md)、[State](state-end-to-end-v5.md)、[Exception](exception-end-to-end-v5.md) の end-to-end instance
4. [Chapter III: shallow-handler calculations](chapter-3-operational-examples-v5.md)
5. [Chapter IV: recursive and derived-deep programs](chapter-4-operational-examples-v5.md)
6. [Language-level main theorem](language-graded-main-theorem-v6.md)
7. [Generic finite theorem](generic-free-extension-theorem-v1.md)
8. [Generic recursive theorem](generic-recursive-resumption-theorem-v1.md)
9. [Functorial extension theorem](functorial-extension-theorem-v5.md) と [package categories](package-categories-v5.md)

各chapter内でも **motivation/examples → definitions → statements → proofs
→ scope/open obligations** の役割を区別する。公開目次はこの役割によって
ページを配置し、数学的本文と研究管理情報を混同しない。

## ステータス記法

査読用の正本ページでは、次の三区分を使う。

- **Lean checked**: 表示した API 宣言がその主張を kernel-check している
- **Paper abstraction**: 構成要素は形式化済みだが、その抽象的包装自体は紙上の記述
- **Boundary / conjecture**: 現在の定理としては主張しない

「文献にある」と「この設定で証明できた」を混同しない。前者は Literature、後者は Claims ledger に記録する。

## Editing and publishing

The notes use [MyST Markdown](https://mystmd.org/) and its book-style website.
See [CONTRIBUTING.md](CONTRIBUTING.md) for local preview and editing rules.
Pushing `main` triggers the GitHub Pages workflow in
`.github/workflows/pages.yml`.
