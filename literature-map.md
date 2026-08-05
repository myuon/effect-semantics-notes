# Literature map

このページでは文献を年代順ではなく、研究上の役割ごとに整理する。
主定理との claim-by-claim 比較は
[Main theorem v3: novelty audit](novelty-audit-main-theorem-v3.md) に移した。

## Verified anchors for the current audit

- Plotkin and Pretnar, [Handling Algebraic Effects](https://arxiv.org/abs/1312.1399):
  free models and handlers as induced homomorphisms.
- Bauer and Pretnar, [An Effect System for Algebraic Effects and Handlers](https://arxiv.org/abs/1306.6316):
  core Eff safety, domain semantics and adequacy.
- Goncharov et al., [Unguarded Recursion on Coinductive Resumptions](https://arxiv.org/abs/1405.0854):
  adjoining free operations to a base monad while preserving complete-Elgot iteration.
- Goncharov, Milius and Rauch, [Complete Elgot Monads and Coalgebraic Resumptions](https://arxiv.org/abs/1603.02148):
  the algebraic structure of complete Elgot resumptions.
- Jaskelioff and Piróg, [Monad Transformers and Modular Algebraic Effects](https://maciejpirog.github.io/papers/what-binds-them-together.pdf):
  correspondence between modular algebraic effects and a class of monad transformers.
- Yoshioka, Sekiyama and Igarashi,
  [Abstracting Effect Systems for Algebraic Effect Handlers](https://arxiv.org/abs/2404.16381):
  effect-algebra-parametric safety.
- Michaelson, Nadathur and Van Wyk,
  [A Modular Approach to Metatheoretic Reasoning for Extensible Languages](https://arxiv.org/abs/2312.14374):
  compositional proof construction for extensible language fragments.

These anchors establish overlap; they do not establish that no closer result exists.

## Free algebraic effects and handlers

調べること:

- free model/free monad と handler-as-homomorphism の標準定理
- shallow handler が標準的自由性からどこまで外れるか

## Graded and category-graded semantics

調べること:

- preordered monoid graded monads と subeffect coercions
- category-graded algebraic theories and handlers
- category grading が本研究に必要か、比較対象に留めるか

## Higher-order and scoped effects

調べること:

- computation-taking operations の generic signatures
- shallow/scoped handlers と generic interpreters
- hefty algebras 等による higher-order effects の algebraic reduction

## Relators and logical relations

調べること:

- monad relators / simulations
- two-sided $(S,T)$-relation lifting
- TT-lifting / biorthogonality
- graph relations と strict morphisms の対応

## Modular operational semantics

調べること:

- operational monad の標準的定義
- syntax/transition systems の modular extension
- effect syntax の追加に対する adequacy-preservation results

## Comparison template

各文献について以下を埋める。

- Citation:
- Semantic objects:
- Supported syntax:
- Handler kind: deep / shallow / scoped / higher-order
- Main theorem:
- Assumptions:
- Observation notion:
- Relation to C-001–C-010:
- What it does not establish:
