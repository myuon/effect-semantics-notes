# Motivation and examples

This part explains the research question before introducing the full semantic
interfaces. Its job is to make the operational phenomena visible: evaluation
order, free requests, shallow forwarding, recursive reinstallation, and the
differences between Writer, State, Exception, and probabilistic choice.

The examples are not substitutes for formal statements. When an example uses
a theorem or definition, its nearby **Lean** link points to the exact checked
declaration. The corresponding general statements are collected in [Theorem
statements](theorem-statements.md).

## Suggested path

1. Read the [research program](research-program-v5.md) for the staged question.
2. Use the [Chapter-I overview](chapter-1-overview-v5.md) to see the base case.
3. Follow the operational examples from Chapters I through IV.
4. Read the Writer, State, Exception, and Random end-to-end calculations when
   comparing concrete models.

## What belongs here

- motivations and informal explanations;
- executable reduction examples and scope calculations;
- explanations of why a definition is needed;
- counterexamples used to expose a design obstruction.

Definitions, theorem statements, and proof obligations belong to the later
parts even when they were discovered through one of these examples.
