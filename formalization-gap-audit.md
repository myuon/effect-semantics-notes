# Open formalization obligations

This is the dependency-ordered working ledger for closing every `[Paper]` and
partial `[Lean: ...]` statement on the canonical proof path.  Repeated
statements in package and proof-detail pages are grouped into one proof
obligation.

## Status vocabulary

- **Existing**: an exact Lean declaration already exists; only note links need repair.
- **Active**: the next dependency currently being formalized.
- **Blocked by statement repair**: the paper statement needs an additional
  premise, a weaker conclusion, or a counterexample before it is a valid Lean target.
- **Pending**: a valid target whose dependencies are not closed yet.

## Dependency-ordered obligations

| order | obligation | note IDs | current status | Lean target / dependency |
|---:|---|---|---|---|
| 1 | general renaming and substitution preservation | `C1-MAIN.1.1`, `C1-MAIN.1.2`, `C1-PROOF.1.2`, `C2-MAIN.1.1` | **Existing** | `HasLanguageVal.subst_preserved`, `HasLanguageComp.subst_preserved`, `subst0_preserved`, `subst2_preserved` |
| 2 | weakening as renaming | `C1-PROOF.1.1` | **Existing** | `rename_preserved` with `LanguageRenPreserves.shift` |
| 3 | canonical forms and unique selected position | `C1-MAIN.2.2`, `C1-PROOF.3.1`, `C1-PROOF.3.2`, `C2-MAIN.2.1` | **Existing, including direct Chapter-II four-way form** | `closed_bool_canonical`, `closed_arr_canonical`, `closed_sum_canonical`, `LanguageProgress.kind_unique`, `LanguageStep.deterministic`, `progressClosed_fourWayExactlyOne` |
| 4 | recursion-free normalization and reducibility | `C1-MAIN.3.1`, `C1-PROOF.4.1`, `C1-PROOF.4.2` | **Lean checked for internal reduction** | reducibility, the fundamental theorem, strong normalization, and arrival at return/boundary are checked; total execution across primitive boundaries still needs a well-founded response kernel |
| 5 | semantic substitution and internal reduction soundness | `C1-MAIN.4.1`, `C1-MAIN.4.2` | **Repaired and checked** | relational tree statements `ProducesLanguageWriterTree.letE`, `internalStepInvariant`; total equality stated only as a conditional presentation |
| 6 | ordered effect upper-bound safety | `C1-MAIN.5.1` | **Checked directly** | `ProducesLanguageWriterTree.effectSound` |
| 7 | concrete base model comparison | `C1-MAIN.7.1`, `C1-MAIN.7.2` | **Individual comparisons checked; typed graded bridge remains** | Writer/State/Exception each have a direct algebra morphism and a separate theorem relating the operational fold to `runClosed`; connecting generic operations to `LanguageSignature` grades remains |
| 8 | empty-free-effect safety | `C2-MAIN.2.2` | **Repaired and checked** | unconditional claim refuted by `empty_free_effect_safety_counterexample`; non-erasing version is `not_exposed_of_interface_absent` |
| 9 | source-tree/generic bridge and graded `FreeExtensionPackage` boundary | `C2-MAIN.5.1`, `C2-MAIN.8.1`–`C2-MAIN.8.3` | **Finite bridge checked; graded identification remains conditional** | `LanguageWriterTree.toFreeExtension_bind` connects the finite source tree to `FreeExtension`; exact source the individual source metatheorems and generic the individual free-extension theorems; $F_eA$ still requires the paper `StrongGradedFreeT` hypothesis |
| 10 | affine handler effect transformation | `C3-MAIN.2.1` | **Checked with sharp boundary** | anchored theorem `anchored_replacement_le_handleWith_of_bounds`; global raw-word version refuted by `replaceFirst_not_monotone` |
| 11 | handler theorem decomposition | `C3-MAIN.6.1`–`C3-MAIN.6.4` | **Checked as separate theorems** | `HasLanguageHandlerState.progressClosed`, `LanguageShallowStep.preserve`, `LanguageWriterTree.Rel.shallow`, `LanguageWriterTree.Rel.shallowTT` |
| 12 | exhaustive derived-deep elimination | `C4-MAIN.4.1`, `C4-PROOF.3.1` | **Checked for source boundary predicate** | `EscapingSelectedRequest`, `exhaustive_no_escaping_selected_request`; no termination premise |
| 13 | ordered recursive effect bound | `C4-PROOF.5.1` | **Checked** | `star_least_fixed_characterization`, `handled_star_le` |
| 14 | partial-handler counterexample | `C4-PROOF.7.1` | **Checked** | `partial_handler_missing_clause_forwards`, `partial_handler_does_not_eliminate_interface` |
| 15 | recursive/derived-deep theorem decomposition | `C4-MAIN.1.1`, `C4-MAIN.7.1`, `C4-MAIN.7.2`, `C4-PROOF.6.1` | **Checked as separate conclusions** | continuity, unfold, leastness, adequacy, result typing, and generic recursive morphism/relation/TT theorems are linked individually |

## Completion rule

An obligation is closed only when:

1. the exact Lean declaration builds without `sorry`;
2. the corresponding note ID links directly to its generated API entry;
3. any stronger paper-only formulation is relabelled `[Boundary]` with the
   missing premise or counterexample stated explicitly; and
4. the public MyST page and generated Lean API link both resolve.
