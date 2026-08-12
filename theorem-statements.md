# Theorem statements

This is the canonical route through the claims of the notes. The chapter pages
state the concrete results first; the abstract pages then isolate the finite
free-extension, recursive-resumption, functorial, relational, and adequacy
transport principles.

## How to read a statement

Every stable statement has an identifier such as `[C2-MAIN.6.1]`. When an exact
Lean theorem exists, a **Lean** link appears in the heading or directly beside
the statement. Follow that link to inspect the checked signature.

The labels have deliberately different force:

- **Lean checked** means the linked declaration checks the stated result;
- **Paper abstraction** means the displayed formulation organizes checked
  components but is not itself one Lean declaration;
- **Boundary**, **conditional**, or **conjecture** means that the missing
  premise or construction remains part of the research problem.

The last class is indexed in [Scope, status, and open
obligations](scope-and-open-obligations.md), rather than being silently folded
into a theorem.

## Reading order

1. Chapter I: safety, normalization, semantic soundness, and base comparison.
2. Chapter II: conservative free extension.
3. Chapter III: shallow-handler preservation and commutation.
4. Chapter IV: recursive completion and derived deep handling.
5. Abstract transport theorems, read only after the concrete chapters.
