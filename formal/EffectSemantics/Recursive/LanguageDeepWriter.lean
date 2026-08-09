import EffectSemantics.Recursive.LanguageFiniteObservation
import EffectSemantics.Recursive.FlatApproximation

namespace EffectSemantics

def LanguageAffineHandler.Exhaustive
    (handler : LanguageAffineHandler) : Prop :=
  ∀ operation, ∃ clause, handler.lookup operation = some clause

/-- A selected request escapes exactly when the current head exposes it and
the handler has no matching clause. -/
def EscapingSelectedRequest (selected : Nat)
    (handler : LanguageAffineHandler) (term : LanguageComp) : Prop :=
  ∃ request : LanguageFreeRequest,
    term.head = .free request ∧ request.interface = selected ∧
      handler.lookup request.operation = none

/-- Exhaustiveness rules out an escaping selected request at every finite
configuration, independently of termination.  Consequently it also holds at
every configuration on any finite execution prefix. -/
theorem LanguageAffineHandler.exhaustive_no_escaping_selected_request
    (exhaustive : handler.Exhaustive) (term : LanguageComp) :
    ¬ EscapingSelectedRequest selected handler term := by
  rintro ⟨request, head, same, missing⟩
  obtain ⟨clause, found⟩ := exhaustive request.operation
  rw [found] at missing
  contradiction

/-- Fuel semantics for the deep handler obtained by recursively reinstalling
the affine shallow handler.  Matching and Writer steps both consume one
finite unfolding. -/
def LanguageComp.observeDeepWriter : Nat → Nat → LanguageAffineHandler →
    LanguageComp → Option (List LanguageVal × LanguageVal)
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
    {term : LanguageComp} {fuel selected : Nat}
    {handler : LanguageAffineHandler}
    {result : List LanguageVal × LanguageVal}
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

def LanguageComp.deepWriterObservation (term : LanguageComp)
    (selected : Nat) (handler : LanguageAffineHandler) :
    StableObservation (List LanguageVal × LanguageVal) where
  observeAt fuel := term.observeDeepWriter fuel selected handler
  stable := LanguageComp.observeDeepWriter_succ_of_some

abbrev LanguageDeepWriterApproximation :=
  FlatApproximation.Carrier LanguageComp (List LanguageVal × LanguageVal)

/-- One unfolding of the recursively reinstalled language handler. -/
def languageDeepWriterFunctional (selected : Nat)
    (handler : LanguageAffineHandler)
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
    (handler : LanguageAffineHandler) : Nat → LanguageDeepWriterApproximation
  | 0 => FlatApproximation.bottom
  | fuel + 1 => languageDeepWriterFunctional selected handler
      (iterateLanguageDeepWriter selected handler fuel)

theorem languageObserveDeepWriter_eq_iterate (fuel selected : Nat)
    (handler : LanguageAffineHandler) (term : LanguageComp) :
    term.observeDeepWriter fuel selected handler =
      iterateLanguageDeepWriter selected handler fuel term := by
  induction fuel generalizing term with
  | zero => rfl
  | succ fuel ih =>
      cases found : term.head <;>
        simp [LanguageComp.observeDeepWriter, iterateLanguageDeepWriter,
          languageDeepWriterFunctional, found, ih]

theorem languageDeepWriterFunctional_continuous (selected : Nat)
    (handler : LanguageAffineHandler) :
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
    (handler : LanguageAffineHandler) : LanguageDeepWriterApproximation :=
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
    (handler : LanguageAffineHandler) :
    LanguageComp → List LanguageVal → LanguageVal → Prop where
  | returned : LanguageDeepWriterRuns selected handler (.ret value) [] value
  | internal : LanguageStep term next →
      LanguageDeepWriterRuns selected handler next log value →
      LanguageDeepWriterRuns selected handler term log value
  | tell (request : LanguageBaseRequest) : term = request.source →
      request.operation = 0 →
      LanguageDeepWriterRuns selected handler (request.resume .unit) log value →
      LanguageDeepWriterRuns selected handler term
        (request.parameter :: log) value
  | matched (request : LanguageFreeRequest) : term = request.source →
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
        simp [LanguageComp.observeDeepWriter, step.to_head, observed]⟩
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
          have source := LanguageComp.head_returned_sound found
          subst term
          exact .returned
      | internal next =>
          simp only [LanguageComp.observeDeepWriter, found] at observed
          obtain ⟨step⟩ := LanguageComp.head_internal_sound found
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
                exact .tell request (LanguageComp.head_base_sound found) writer
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
                exact .matched request (LanguageComp.head_free_sound found) same
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

/-- The only extra base-specific assumption used by typed Writer runs. -/
structure LanguageWriterResponseUnit (sig : LanguageSignature) : Prop where
  responseUnit : ∀ {parameterTy responseTy},
    sig.base 0 = some ⟨parameterTy, responseTy⟩ → responseTy = .unit

/-- Every finite result of the derived deep handler retains the source result
type.  The recursive proof uses ordinary preservation at internal steps and
the already checked affine matching-reduct theorem. -/
theorem LanguageDeepWriterRuns.result_typed
    (writerSig : LanguageWriterResponseUnit sig)
    (handlerTyping : HasLanguageAffineHandler sig [] selected handler replacement)
    (runs : LanguageDeepWriterRuns selected handler term log value)
    (typing : HasLanguageComp sig [] term resultTy effect) :
    Nonempty (HasLanguageVal sig [] value resultTy) := by
  induction runs generalizing effect with
  | returned => exact ⟨typing.returnView.valueTyping⟩
  | internal step runs ih => exact ih (step.preserve typing)
  | tell request exposed writer runs ih =>
      rw [exposed] at typing
      let requestTyping := typing.exposedBaseView
      have operationLookup : sig.base 0 =
          some ⟨requestTyping.parameterTy, requestTyping.responseTy⟩ := by
        simpa [writer] using requestTyping.lookup
      have responseEq := writerSig.responseUnit operationLookup
      have unitTyping : HasLanguageVal sig [] (.unit : LanguageVal)
          requestTyping.responseTy := by
        rw [responseEq]
        exact .unit
      exact ih (requestTyping.resumeTyping unitTyping)
  | matched request exposed same found runs ih =>
      rw [exposed] at typing
      exact ih (handlerTyping.answerWithTyping typing same found)

theorem languageDeepWriterSemantics_result_typed
    (writerSig : LanguageWriterResponseUnit sig)
    (handlerTyping : HasLanguageAffineHandler sig [] selected handler replacement)
    (typing : HasLanguageComp sig [] term resultTy effect)
    (observed : languageDeepWriterSemantics selected handler term =
      some (log, value)) :
    Nonempty (HasLanguageVal sig [] value resultTy) :=
  (language_deep_writer_semantic_adequacy.mpr observed).result_typed
    writerSig handlerTyping typing

end EffectSemantics
