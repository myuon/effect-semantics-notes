import EffectSemantics.Recursive.LanguageRequests
import EffectSemantics.Recursive.LanguageFiniteObservation
import EffectSemantics.Recursive.FlatApproximation

namespace EffectSemantics

def RecLanguageHandlerExhaustive
    (handler : LanguageAffineHandler .recursive) : Prop :=
  ∀ operation, ∃ clause, handler.lookup operation = some clause

/-- A selected request escapes exactly when the current head exposes it and
the handler has no matching clause. -/
def EscapingSelectedRequest (selected : Nat)
    (handler : LanguageAffineHandler .recursive) (term : RecLanguageComp) : Prop :=
  ∃ request : RecLanguageFreeRequest,
    term.head = .free request ∧ request.interface = selected ∧
      handler.lookup request.operation = none

/-- Exhaustiveness rules out an escaping selected request at every finite
configuration, independently of termination.  Consequently it also holds at
every configuration on any finite execution prefix. -/
theorem recLanguageHandlerExhaustive_no_escaping_selected_request
    (exhaustive : RecLanguageHandlerExhaustive handler) (term : RecLanguageComp) :
    ¬ EscapingSelectedRequest selected handler term := by
  rintro ⟨request, head, same, missing⟩
  obtain ⟨clause, found⟩ := exhaustive request.operation
  rw [found] at missing
  contradiction

/-- Fuel semantics for the deep handler obtained by recursively reinstalling
the affine shallow handler.  Matching and Writer steps both consume one
finite unfolding. -/
def LanguageComp.observeDeepWriter : Nat → Nat → LanguageAffineHandler .recursive →
    RecLanguageComp → Option (List RecLanguageVal × RecLanguageVal)
  | 0, _, _, _ => none
  | fuel + 1, selected, handler, term =>
      match term.head with
      | .returned value => some ([], value)
      | .internal next => next.observeDeepWriter fuel selected handler
      | .base request =>
          if request.operation = 0 then
            ((request.resume .unit).observeDeepWriter fuel selected handler).map
              (fun result => (request.parameter :: result.1, result.2))
          else none
      | .free request =>
          if request.interface = selected then
            match handler.lookup request.operation with
            | some clause =>
                (request.answerWith clause).observeDeepWriter fuel selected handler
            | none => none
          else none
      | .stuck => none

theorem LanguageComp.observeDeepWriter_succ_of_some
    {term : RecLanguageComp} {fuel selected : Nat}
    {handler : LanguageAffineHandler .recursive}
    {result : List RecLanguageVal × RecLanguageVal}
    (observed : term.observeDeepWriter fuel selected handler = some result) :
    term.observeDeepWriter (fuel + 1) selected handler = some result := by
  induction fuel generalizing term result with
  | zero => simp [LanguageComp.observeDeepWriter] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value =>
          simpa [LanguageComp.observeDeepWriter, found] using observed
      | internal next =>
          simp only [LanguageComp.observeDeepWriter, found] at observed ⊢
          exact ih observed
      | base request =>
          by_cases writer : request.operation = 0
          · simp only [LanguageComp.observeDeepWriter, found, writer, if_pos,
              Option.map_eq_some_iff] at observed ⊢
            obtain ⟨tail, tailObserved, transformed⟩ := observed
            exact ⟨tail, ih tailObserved, transformed⟩
          · simp [LanguageComp.observeDeepWriter, found, writer] at observed
      | free request =>
          by_cases same : request.interface = selected
          · cases clauseFound : handler.lookup request.operation with
            | none =>
                simp [LanguageComp.observeDeepWriter, found, same, clauseFound]
                  at observed
            | some clause =>
                simp only [LanguageComp.observeDeepWriter, found, same, if_pos,
                  clauseFound] at observed ⊢
                exact ih observed
          · simp [LanguageComp.observeDeepWriter, found, same] at observed
      | stuck => simp [LanguageComp.observeDeepWriter, found] at observed

def LanguageComp.deepWriterObservation (term : RecLanguageComp)
    (selected : Nat) (handler : LanguageAffineHandler .recursive) :
    StableObservation (List RecLanguageVal × RecLanguageVal) where
  observeAt fuel := term.observeDeepWriter fuel selected handler
  stable := LanguageComp.observeDeepWriter_succ_of_some

abbrev LanguageDeepWriterApproximation :=
  FlatApproximation.Carrier RecLanguageComp (List RecLanguageVal × RecLanguageVal)

/-- One unfolding of the recursively reinstalled language handler. -/
def languageDeepWriterFunctional (selected : Nat)
    (handler : LanguageAffineHandler .recursive)
    (next : LanguageDeepWriterApproximation) : LanguageDeepWriterApproximation :=
  fun term =>
    match term.head with
    | .returned value => some ([], value)
    | .internal term' => next term'
    | .base request =>
        if request.operation = 0 then
          (next (request.resume .unit)).map
            (fun result => (request.parameter :: result.1, result.2))
        else none
    | .free request =>
        if request.interface = selected then
          match handler.lookup request.operation with
          | some clause => next (request.answerWith clause)
          | none => none
        else none
    | .stuck => none

theorem languageDeepWriterFunctional_monotone
    (bound : FlatApproximation.LE lower upper) :
    FlatApproximation.LE
      (languageDeepWriterFunctional selected handler lower)
      (languageDeepWriterFunctional selected handler upper) := by
  intro term result observed
  unfold languageDeepWriterFunctional at observed ⊢
  cases found : term.head with
  | returned value => simpa [found] using observed
  | internal next =>
      simp only [found] at observed ⊢
      exact bound next result observed
  | base request =>
      by_cases writer : request.operation = 0
      · simp only [found, writer, if_pos, Option.map_eq_some_iff] at observed ⊢
        obtain ⟨tail, finite, transformed⟩ := observed
        exact ⟨tail, bound _ _ finite, transformed⟩
      · simp [found, writer] at observed
  | free request =>
      by_cases same : request.interface = selected
      · cases clauseFound : handler.lookup request.operation with
        | none => simp [found, same, clauseFound] at observed
        | some clause =>
            simp only [found, same, if_pos, clauseFound] at observed ⊢
            exact bound _ _ observed
      · simp [found, same] at observed
  | stuck => simp [found] at observed

def iterateLanguageDeepWriter (selected : Nat)
    (handler : LanguageAffineHandler .recursive) : Nat → LanguageDeepWriterApproximation
  | 0 => FlatApproximation.bottom
  | fuel + 1 => languageDeepWriterFunctional selected handler
      (iterateLanguageDeepWriter selected handler fuel)

theorem languageObserveDeepWriter_eq_iterate (fuel selected : Nat)
    (handler : LanguageAffineHandler .recursive) (term : RecLanguageComp) :
    term.observeDeepWriter fuel selected handler =
      iterateLanguageDeepWriter selected handler fuel term := by
  induction fuel generalizing term with
  | zero => rfl
  | succ fuel ih =>
      cases found : term.head <;>
        simp [LanguageComp.observeDeepWriter, iterateLanguageDeepWriter,
          languageDeepWriterFunctional, found, ih]

theorem languageDeepWriterFunctional_continuous (selected : Nat)
    (handler : LanguageAffineHandler .recursive) :
    FlatApproximation.OmegaContinuous
      (languageDeepWriterFunctional selected handler) where
  monotone := languageDeepWriterFunctional_monotone
  preservesSup := by
    intro chain
    apply FlatApproximation.le_antisymm
    · intro term result observed
      unfold languageDeepWriterFunctional at observed
      cases found : term.head with
      | returned value =>
          exact FlatApproximation.Chain.sup_of_observed _ (index := 0)
            (by simpa [languageDeepWriterFunctional, found] using observed)
      | internal next =>
          simp only [found] at observed
          obtain ⟨index, finite⟩ := chain.sup_some_witness observed
          exact FlatApproximation.Chain.sup_of_observed _ (index := index)
            (by simpa [languageDeepWriterFunctional, found] using finite)
      | base request =>
          by_cases writer : request.operation = 0
          · simp only [found, writer, if_pos, Option.map_eq_some_iff]
              at observed
            obtain ⟨tail, tailObserved, transformed⟩ := observed
            obtain ⟨index, finite⟩ := chain.sup_some_witness tailObserved
            apply FlatApproximation.Chain.sup_of_observed _ (index := index)
            simp only [languageDeepWriterFunctional, found, writer, if_pos,
              Option.map_eq_some_iff]
            exact ⟨tail, finite, transformed⟩
          · simp [found, writer] at observed
      | free request =>
          by_cases same : request.interface = selected
          · cases clauseFound : handler.lookup request.operation with
            | none => simp [found, same, clauseFound] at observed
            | some clause =>
                simp only [found, same, if_pos, clauseFound] at observed
                obtain ⟨index, finite⟩ := chain.sup_some_witness observed
                apply FlatApproximation.Chain.sup_of_observed _ (index := index)
                simpa [languageDeepWriterFunctional, found, same, clauseFound]
                  using finite
          · simp [found, same] at observed
      | stuck => simp [found] at observed
    · intro term result observed
      obtain ⟨index, finite⟩ :=
        FlatApproximation.Chain.sup_some_witness _ observed
      exact languageDeepWriterFunctional_monotone (chain.le_sup index)
        term result finite

noncomputable def languageDeepWriterSemantics (selected : Nat)
    (handler : LanguageAffineHandler .recursive) : LanguageDeepWriterApproximation :=
  FlatApproximation.lfp (languageDeepWriterFunctional selected handler)
    (languageDeepWriterFunctional_continuous selected handler)

theorem languageDeepWriterSemantics_unfold :
    languageDeepWriterFunctional selected handler
      (languageDeepWriterSemantics selected handler) =
      languageDeepWriterSemantics selected handler :=
  FlatApproximation.lfp_unfold
    (languageDeepWriterFunctional_continuous selected handler)

theorem languageDeepWriterSemantics_le_prefixed
    (prefixed : FlatApproximation.LE
      (languageDeepWriterFunctional selected handler candidate) candidate) :
    FlatApproximation.LE (languageDeepWriterSemantics selected handler) candidate :=
  FlatApproximation.lfp_le_prefixed
    (languageDeepWriterFunctional_continuous selected handler) prefixed

/-- Direct terminating runs of the recursively reinstalled shallow handler. -/
inductive LanguageDeepWriterRuns (selected : Nat)
    (handler : LanguageAffineHandler .recursive) :
    RecLanguageComp → List RecLanguageVal → RecLanguageVal → Prop where
  | returned : LanguageDeepWriterRuns selected handler (.ret value) [] value
  | internal : LanguageStep term next →
      LanguageDeepWriterRuns selected handler next log value →
      LanguageDeepWriterRuns selected handler term log value
  | tell (request : RecLanguageBaseRequest) : term = request.source →
      request.operation = 0 →
      LanguageDeepWriterRuns selected handler (request.resume .unit) log value →
      LanguageDeepWriterRuns selected handler term
        (request.parameter :: log) value
  | matched (request : RecLanguageFreeRequest) : term = request.source →
      request.interface = selected →
      handler.lookup request.operation = some clause →
      LanguageDeepWriterRuns selected handler
        (request.answerWith clause) log value →
      LanguageDeepWriterRuns selected handler term log value

theorem LanguageDeepWriterRuns.to_observation
    (runs : LanguageDeepWriterRuns selected handler term log value) :
    ∃ fuel, term.observeDeepWriter fuel selected handler = some (log, value) := by
  induction runs with
  | returned => exact ⟨1, rfl⟩
  | internal step runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      exact ⟨fuel + 1, by
        simp [LanguageComp.observeDeepWriter, step.to_recHead, observed]⟩
  | tell request exposed writer runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [exposed]
      simp [LanguageComp.observeDeepWriter, writer, observed]
  | matched request exposed same found runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [exposed]
      simp [LanguageComp.observeDeepWriter, same, found, observed]

theorem LanguageComp.observeDeepWriter_reflects
    (observed : term.observeDeepWriter fuel selected handler = some (log, value)) :
    LanguageDeepWriterRuns selected handler term log value := by
  induction fuel generalizing term log value with
  | zero => simp [LanguageComp.observeDeepWriter] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned result =>
          simp [LanguageComp.observeDeepWriter, found] at observed
          obtain ⟨rfl, rfl⟩ := observed
          have source := RecLanguageComp.head_returned_sound found
          subst term
          exact .returned
      | internal next =>
          simp only [LanguageComp.observeDeepWriter, found] at observed
          obtain ⟨step⟩ := RecLanguageComp.head_internal_sound found
          exact .internal step (ih observed)
      | base request =>
          by_cases writer : request.operation = 0
          · simp only [LanguageComp.observeDeepWriter, found, writer, if_pos,
              Option.map_eq_some_iff] at observed
            obtain ⟨tail, tailObserved, transformed⟩ := observed
            cases tail with
            | mk tailLog tailValue =>
                simp at transformed
                obtain ⟨rfl, rfl⟩ := transformed
                exact .tell request (RecLanguageComp.head_base_sound found) writer
                  (ih tailObserved)
          · simp [LanguageComp.observeDeepWriter, found, writer] at observed
      | free request =>
          by_cases same : request.interface = selected
          · cases clauseFound : handler.lookup request.operation with
            | none =>
                simp [LanguageComp.observeDeepWriter, found, same, clauseFound]
                  at observed
            | some clause =>
                simp only [LanguageComp.observeDeepWriter, found, same, if_pos,
                  clauseFound] at observed
                exact .matched request (RecLanguageComp.head_free_sound found) same
                  clauseFound (ih observed)
          · simp [LanguageComp.observeDeepWriter, found, same] at observed
      | stuck => simp [LanguageComp.observeDeepWriter, found] at observed

theorem language_deep_writer_finite_adequacy :
    LanguageDeepWriterRuns selected handler term log value ↔
      ∃ fuel, term.observeDeepWriter fuel selected handler = some (log, value) :=
  ⟨LanguageDeepWriterRuns.to_observation,
    fun ⟨_fuel, observed⟩ => LanguageComp.observeDeepWriter_reflects observed⟩

theorem iterateLanguageDeepWriter_eq_flat (fuel : Nat) :
    iterateLanguageDeepWriter selected handler fuel =
      FlatApproximation.iterate
        (languageDeepWriterFunctional selected handler) fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp [iterateLanguageDeepWriter, FlatApproximation.iterate, ih]

theorem languageDeepWriterSemantics_of_observed
    (observed : term.observeDeepWriter fuel selected handler = some result) :
    languageDeepWriterSemantics selected handler term = some result := by
  unfold languageDeepWriterSemantics FlatApproximation.lfp
  apply FlatApproximation.Chain.sup_of_observed _ (index := fuel)
  change FlatApproximation.iterate
      (languageDeepWriterFunctional selected handler) fuel term = some result
  rw [← iterateLanguageDeepWriter_eq_flat]
  rwa [languageObserveDeepWriter_eq_iterate] at observed

theorem languageDeepWriterSemantics_some_witness
    (observed : languageDeepWriterSemantics selected handler term = some result) :
    ∃ fuel, term.observeDeepWriter fuel selected handler = some result := by
  unfold languageDeepWriterSemantics FlatApproximation.lfp at observed
  obtain ⟨fuel, finite⟩ :=
    FlatApproximation.Chain.sup_some_witness _ observed
  refine ⟨fuel, ?_⟩
  rw [languageObserveDeepWriter_eq_iterate, iterateLanguageDeepWriter_eq_flat]
  exact finite

/-- Adequacy of the least-fixed-point denotation, including recursive source
programs: a finite Writer result is denoted exactly when the derived deep
handler has a terminating operational run with that result. -/
theorem language_deep_writer_semantic_adequacy :
    LanguageDeepWriterRuns selected handler term log value ↔
      languageDeepWriterSemantics selected handler term = some (log, value) := by
  constructor
  · intro runs
    obtain ⟨fuel, observed⟩ := runs.to_observation
    exact languageDeepWriterSemantics_of_observed observed
  · intro observed
    obtain ⟨fuel, finite⟩ := languageDeepWriterSemantics_some_witness observed
    exact LanguageComp.observeDeepWriter_reflects finite

/-- Typing obligations at the two visible recursive boundaries.  Internal
steps need no extra assumption: ordinary preservation already covers them. -/
structure LanguageRecursiveBoundaryTypingCert (sig : LanguageSignature)
    (selected : Nat) (handler : LanguageAffineHandler .recursive)
    (replacement : EffectLanguage) where
  baseResume : ∀ {request : RecLanguageBaseRequest} {resultTy effect},
    request.operation = 0 →
    HasLanguageComp sig [] request.source resultTy effect →
    HasLanguageComp sig [] (request.resume .unit) resultTy effect
  matchedAnswer : ∀ {request : RecLanguageFreeRequest} {clause resultTy effect},
    request.interface = selected →
    handler.lookup request.operation = some clause →
    HasLanguageComp sig [] request.source resultTy effect →
    HasLanguageComp sig [] (request.answerWith clause) resultTy
      (EffectLanguage.handleWith selected replacement effect)

/-- Every finite result of the derived deep handler retains the source result
type.  The recursive proof uses ordinary preservation at internal steps and
the already checked affine matching-reduct theorem. -/
theorem LanguageDeepWriterRuns.result_typed
    (boundaries : LanguageRecursiveBoundaryTypingCert sig selected handler replacement)
    (runs : LanguageDeepWriterRuns selected handler term log value)
    (typing : HasLanguageComp sig [] term resultTy effect) :
    Nonempty (HasLanguageVal sig [] value resultTy) := by
  induction runs generalizing effect with
  | returned => exact ⟨typing.returnView.valueTyping⟩
  | internal step runs ih => exact ih (step.preserve typing)
  | tell request exposed writer runs ih =>
      rw [exposed] at typing
      exact ih (boundaries.baseResume writer typing)
  | matched request exposed same found runs ih =>
      rw [exposed] at typing
      exact ih (boundaries.matchedAnswer same found typing)

theorem languageDeepWriterSemantics_result_typed
    (boundaries : LanguageRecursiveBoundaryTypingCert sig selected handler replacement)
    (typing : HasLanguageComp sig [] term resultTy effect)
    (observed : languageDeepWriterSemantics selected handler term =
      some (log, value)) :
    Nonempty (HasLanguageVal sig [] value resultTy) :=
  (language_deep_writer_semantic_adequacy.mpr observed).result_typed
    boundaries typing

end EffectSemantics
