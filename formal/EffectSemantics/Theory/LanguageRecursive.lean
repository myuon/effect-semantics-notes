import EffectSemantics.Theory.LanguageFinite
import EffectSemantics.Theory.LanguageGenericRecursive
import EffectSemantics.Recursive.LanguageDeepWriter

namespace EffectSemantics

/-!
# Recursive Writer instance

This module discharges the generic recursive package for the ordered
language-graded Writer observation and proves the typed observation pole.
-/

/-- The recursive completion of the finite ordered-language theorem for the
Writer base observation.  Its base-specific premises are isolated at the two
visible recursive boundaries: the Writer response and a matched free request. -/
structure LanguageRecursiveTheory
    (sig : LanguageSignature) (selected : Nat)
    (handler : LanguageAffineHandler .recursive) (replacement : EffectLanguage) where
  finite : LanguageFiniteTheory sig
  boundaries : LanguageRecursiveBoundaryTyping sig selected handler replacement
  continuous : FlatApproximation.OmegaContinuous
    (languageDeepWriterFunctional selected handler)
  unfold : languageDeepWriterFunctional selected handler
      (languageDeepWriterSemantics selected handler) =
    languageDeepWriterSemantics selected handler
  least : ∀ {candidate}, FlatApproximation.LE
      (languageDeepWriterFunctional selected handler candidate) candidate →
    FlatApproximation.LE (languageDeepWriterSemantics selected handler) candidate
  adequacy : ∀ {term log value},
    LanguageDeepWriterRuns selected handler term log value ↔
      languageDeepWriterSemantics selected handler term = some (log, value)
  fundamental : ∀ {term resultTy effect log value},
    [] ⊢[sig] term : resultTy ! effect →
    languageDeepWriterSemantics selected handler term = some (log, value) →
    Nonempty ([] ⊢[sig] value :ᵥ resultTy)
  poleAdmissible : ∀ (pole : RecLanguageComp →
      (List RecLanguageVal × RecLanguageVal) → Prop),
    FlatApproximation.Admissible (FlatApproximation.Satisfies pole)

def LanguageTypedWriterPole (sig : LanguageSignature) :
    RecLanguageComp → (List RecLanguageVal × RecLanguageVal) → Prop :=
  fun term outcome => ∀ (resultTy : LanguageTy) (effect : EffectLanguage),
    [] ⊢[sig] term : resultTy ! effect →
      Nonempty ([] ⊢[sig] outcome.2 :ᵥ resultTy)

theorem languageDeepWriterLayer_preserves_typedPole
    (boundaries : LanguageRecursiveBoundaryTyping sig selected handler replacement)
    (approximation : LanguageDeepWriterApproximation)
    (good : FlatApproximation.Satisfies (LanguageTypedWriterPole sig)
      approximation) :
    FlatApproximation.Satisfies (LanguageTypedWriterPole sig)
      (languageDeepWriterFunctional selected handler approximation) := by
  intro term outcome observed resultTy effect typing
  unfold languageDeepWriterFunctional at observed
  cases found : term.head with
  | returned value =>
      simp only [found] at observed
      have outcomeEq : ([], value) = outcome := Option.some.inj observed
      subst outcome
      have source := RecLanguageComp.head_returned_sound found
      subst term
      exact ⟨typing.returnView.valueTyping⟩
  | internal next =>
      simp only [found] at observed
      obtain ⟨step⟩ := RecLanguageComp.head_internal_sound found
      exact good next outcome observed resultTy effect (step.preserve typing)
  | base request =>
      by_cases writer : request.operation = 0
      · simp only [found, writer, if_pos, Option.map_eq_some_iff] at observed
        obtain ⟨tail, finite, transformed⟩ := observed
        have source := RecLanguageComp.head_base_sound found
        rw [source] at typing
        have tailGood := good (request.resume .unit) tail finite resultTy effect
          (boundaries.baseResume writer typing)
        cases tail with
        | mk tailLog tailValue =>
            simp at transformed
            obtain ⟨rfl, rfl⟩ := transformed
            exact tailGood
      · simp [found, writer] at observed
  | free request =>
      by_cases same : request.interface = selected
      · cases clauseFound : handler.lookup request.operation with
        | none => simp [found, same, clauseFound] at observed
        | some clause =>
            simp only [found, same, if_pos, clauseFound] at observed
            have source := RecLanguageComp.head_free_sound found
            rw [source] at typing
            exact good (request.answerWith clause) outcome observed resultTy
              (EffectLanguage.handleWith selected replacement effect)
              (boundaries.matchedAnswer same clauseFound typing)
      · simp [found, same] at observed
  | stuck => simp [found] at observed

noncomputable def languageWriterRecursiveModel
    (boundaries : LanguageRecursiveBoundaryTyping sig selected handler replacement) :
    LanguageRecursiveModel sig (List RecLanguageVal × RecLanguageVal) where
  source := languageSourceTheory sig
  functional := languageDeepWriterFunctional selected handler
  continuous := languageDeepWriterFunctional_continuous selected handler
  Runs term outcome := LanguageDeepWriterRuns selected handler term outcome.1 outcome.2
  finiteAdequacy := by
    intro term outcome
    rcases outcome with ⟨log, value⟩
    rw [language_deep_writer_finite_adequacy]
    constructor <;> rintro ⟨fuel, observed⟩ <;> refine ⟨fuel, ?_⟩
    · change FlatApproximation.iterate
        (languageDeepWriterFunctional selected handler) fuel term =
          some (log, value)
      rw [← iterateLanguageDeepWriter_eq_flat]
      rwa [← languageObserveDeepWriter_eq_iterate]
    · change LanguageComp.observeDeepWriter fuel selected handler term =
        some (log, value)
      rw [languageObserveDeepWriter_eq_iterate,
        iterateLanguageDeepWriter_eq_flat]
      exact observed
  pole := LanguageTypedWriterPole sig
  layerPreservesPole := languageDeepWriterLayer_preserves_typedPole
    boundaries

/-- Recursive ordered-language structure-preservation theorem.  Shallow
handling supplies the one-layer functional; recursion supplies its least
fixed point.  Adequacy and the ground fundamental property survive this
completion. -/
noncomputable def languageRecursiveStructurePreservation
    (boundaries : LanguageRecursiveBoundaryTyping sig selected handler replacement) :
    LanguageRecursiveTheory sig selected handler replacement where
  finite := languageFiniteStructurePreservation sig
  boundaries := boundaries
  continuous := languageDeepWriterFunctional_continuous selected handler
  unfold := languageDeepWriterSemantics_unfold
  least := languageDeepWriterSemantics_le_prefixed
  adequacy := language_deep_writer_semantic_adequacy
  fundamental := fun typing observed =>
    languageDeepWriterSemantics_result_typed boundaries
      typing observed
  poleAdmissible := FlatApproximation.satisfies_admissible

end EffectSemantics
