# Motivation and examples

This part explains the research question before introducing the full semantic
interfaces. Its job is to make the operational phenomena visible: evaluation
order, free requests, shallow forwarding, recursive reinstallation, and the
differences between Writer, State, Exception, and probabilistic choice.

The examples are not substitutes for formal statements. When an example uses
a theorem or definition, its nearby **Lean** link points to the exact checked
declaration. The corresponding general statements are collected in [Theorem
statements](theorem-statements.md).

## Read this part from top to bottom

1. [Research question and staged development](research-program-v5.md) explains
   why the extension is split into base effects, free operations, shallow
   handlers, and recursion.
2. [How the development proceeds](chapter-method-v5.md) explains what must be
   supplied and proved at each stage.
3. [Why start with concrete base languages?](chapter-1-overview-v5.md) fixes the
   baseline and the questions carried into later stages.
4. [Base-language behavior](chapter-1-operational-examples-v5.md) introduces
   evaluation order through Writer, State, Exception, and Random programs.
5. [Free-operation behavior](chapter-2-operational-examples-v5.md) adds requests
   without handling them yet.
6. The [Writer](writer-end-to-end-v5.md), [State](state-end-to-end-v5.md),
   [Exception](exception-end-to-end-v5.md), and [Random](random-end-to-end-v5.md)
   case studies compare how the same extension interacts with different base
   effects.
7. [Shallow-handler behavior](chapter-3-operational-examples-v5.md) then adds
   matching and forwarding.
8. [Recursive behavior](chapter-4-operational-examples-v5.md) finally shows how
   repeated shallow handling yields the intended deep behavior.

## What belongs here

- motivations and informal explanations;
- executable reduction examples and scope calculations;
- explanations of why a definition is needed;
- counterexamples used to expose a design obstruction.

Definitions, theorem statements, and proof obligations belong to the later
parts even when they were discovered through one of these examples.

After these examples, continue with [Formal setting and
definitions](formal-setting-and-definitions.md), which assigns precise syntax
and semantics to the behavior just observed.
