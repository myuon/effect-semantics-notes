# Theorem statements

This is the canonical route through the claims of the notes. The chapter pages
state the concrete results first; the abstract pages then isolate the finite
free-extension, recursive-resumption, functorial, relational, and adequacy
transport principles.

## How to read a statement

Every stable statement has an identifier such as `[C2-MAIN.6.1]`. When Lean
checks the displayed statement, its declaration is cited in the **Proof**
position: the checked term is the proof, so the notes do not repeat a parallel
paper proof. Follow the link to inspect the exact signature and proof.

A separate proof or **Lean correspondence** paragraph appears only when no Lean
proof exists, or when the displayed mathematical statement is stronger,
weaker, or more abstract than the linked declaration. In the latter case the
paragraph says explicitly which part is checked and what additional step or
assumption remains on paper.

The labels have deliberately different force:

- **Lean checked** means the linked declaration checks the stated result;
- **Paper abstraction** means the displayed formulation organizes checked
  components but is not itself one Lean declaration;
- **Boundary**, **conditional**, or **conjecture** means that the missing
  premise or construction remains part of the research problem.

The last class is indexed in [Scope, status, and open
obligations](scope-and-open-obligations.md), rather than being silently folded
into a theorem.

## Read this part from top to bottom

1. [Base-language theorems](chapter-1-main-results-v5.md): substitution,
   preservation, progress, normalization, soundness, and model comparison.
2. [Free-extension theorems](chapter-2-main-results-v5.md): operational and
   denotational conservativity after adding requests.
3. [Shallow-handler theorems](chapter-3-main-results-v5.md): preservation,
   effect transformation, and operational/denotational commutation.
4. [Recursive theorems](chapter-4-main-results-v5.md): finite and limit
   adequacy, derived/deep coincidence, and interface elimination.
5. [The main language theorem](language-graded-main-theorem-v6.md) assembles
   those four concrete stages.
6. The [abstract finite](generic-free-extension-theorem-v1.md) and
   [abstract recursive](generic-recursive-resumption-theorem-v1.md) theorems
   factor out the reusable transport principles.
7. The [functorial theorem](functorial-extension-theorem-v5.md) and
   [categorical formulation](package-categories-v5.md) state the strongest
   abstract view and its exact boundary.

For proof details, continue with [Proofs and
dependencies](proofs-and-dependencies.md).
