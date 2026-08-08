import EffectSemantics.Recursive.WriterObservation
import EffectSemantics.Operational.ShallowHandler

namespace EffectSemantics

/-- Finite observations of the deep handler derived by recursive
reinstallation of the direct shallow match. Unhandled requests have no closed
Writer observation here; they belong to the richer outward-boundary model. -/
def Comp.observeDeepWriter : Nat → Nat → AffineHandler → Comp →
    Option (List Val × Val)
  | 0, _, _, _ => none
  | fuel + 1, interface, handler, term =>
      match term.head with
      | .returned value => some ([], value)
      | .internal next => next.observeDeepWriter fuel interface handler
      | .base request =>
          if request.operation = 0 then
            ((request.resume .unit).observeDeepWriter fuel interface handler).map
              (fun result => (request.parameter :: result.1, result.2))
          else none
      | .free request =>
          if request.interface = interface then
            match handler.lookup request.operation with
            | some clause =>
                (request.answerWith clause).observeDeepWriter fuel interface handler
            | none => none
          else none
      | .stuck => none

abbrev DeepWriterApproximation := Comp → Option (List Val × Val)

/-- One semantic unfolding of the recursively reinstalled handler. -/
def deepWriterFunctional (interface : Nat) (handler : AffineHandler)
    (next : DeepWriterApproximation) : DeepWriterApproximation :=
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
        if request.interface = interface then
          match handler.lookup request.operation with
          | some clause => next (request.answerWith clause)
          | none => none
        else none
    | .stuck => none

def iterateDeepWriter (interface : Nat) (handler : AffineHandler) :
    Nat → DeepWriterApproximation
  | 0 => fun _ => none
  | fuel + 1 => deepWriterFunctional interface handler
      (iterateDeepWriter interface handler fuel)

theorem observeDeepWriter_eq_iterate (fuel interface : Nat)
    (handler : AffineHandler) (term : Comp) :
    term.observeDeepWriter fuel interface handler =
      iterateDeepWriter interface handler fuel term := by
  induction fuel generalizing term with
  | zero => rfl
  | succ fuel ih =>
      cases found : term.head with
      | returned value => simp [Comp.observeDeepWriter, iterateDeepWriter,
          deepWriterFunctional, found]
      | internal next => simp [Comp.observeDeepWriter, iterateDeepWriter,
          deepWriterFunctional, found, ih]
      | base request =>
          by_cases selected : request.operation = 0
          · simp [Comp.observeDeepWriter, iterateDeepWriter,
              deepWriterFunctional, found, selected, ih]
          · simp [Comp.observeDeepWriter, iterateDeepWriter,
              deepWriterFunctional, found, selected]
      | free request =>
          by_cases same : request.interface = interface
          · cases clauseFound : handler.lookup request.operation <;>
              simp [Comp.observeDeepWriter, iterateDeepWriter,
                deepWriterFunctional, found, same, clauseFound, ih]
          · simp [Comp.observeDeepWriter, iterateDeepWriter,
              deepWriterFunctional, found, same]
      | stuck => simp [Comp.observeDeepWriter, iterateDeepWriter,
          deepWriterFunctional, found]

def DeepWriterApproximation.LE
    (lower upper : DeepWriterApproximation) : Prop :=
  ∀ term result, lower term = some result → upper term = some result

theorem deepWriterFunctional_monotone
    (bound : DeepWriterApproximation.LE lower upper) :
    DeepWriterApproximation.LE
      (deepWriterFunctional interface handler lower)
      (deepWriterFunctional interface handler upper) := by
  intro term result observed
  unfold deepWriterFunctional at observed ⊢
  cases found : term.head with
  | returned value => simpa [found] using observed
  | internal next =>
      simp only [found] at observed ⊢
      exact bound next result observed
  | base request =>
      by_cases selected : request.operation = 0
      · simp only [found, selected, if_pos, Option.map_eq_some_iff]
          at observed ⊢
        obtain ⟨tail, tailObserved, transformed⟩ := observed
        exact ⟨tail, bound _ _ tailObserved, transformed⟩
      · simp [found, selected] at observed
  | free request =>
      by_cases same : request.interface = interface
      · cases clauseFound : handler.lookup request.operation with
        | none => simp [found, same, clauseFound] at observed
        | some clause =>
            simp only [found, same, if_pos, clauseFound] at observed ⊢
            exact bound _ _ observed
      · simp [found, same] at observed
  | stuck => simp [found] at observed

theorem Comp.observeDeepWriter_succ_of_some
    {term : Comp} {fuel interface : Nat} {handler : AffineHandler}
    {result : List Val × Val}
    (observed : term.observeDeepWriter fuel interface handler = some result) :
    term.observeDeepWriter (fuel + 1) interface handler = some result := by
  induction fuel generalizing term result with
  | zero => simp [Comp.observeDeepWriter] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value => simpa [Comp.observeDeepWriter, found] using observed
      | internal next =>
          simp only [Comp.observeDeepWriter, found] at observed ⊢
          exact ih observed
      | base request =>
          by_cases selected : request.operation = 0
          · simp only [Comp.observeDeepWriter, found, selected, if_pos,
              Option.map_eq_some_iff] at observed ⊢
            obtain ⟨tail, tailObserved, transformed⟩ := observed
            exact ⟨tail, ih tailObserved, transformed⟩
          · simp [Comp.observeDeepWriter, found, selected] at observed
      | free request =>
          by_cases same : request.interface = interface
          · cases clauseFound : handler.lookup request.operation with
            | none =>
                simp [Comp.observeDeepWriter, found, same, clauseFound] at observed
            | some clause =>
                simp only [Comp.observeDeepWriter, found, same, if_pos,
                  clauseFound] at observed ⊢
                exact ih observed
          · simp [Comp.observeDeepWriter, found, same] at observed
      | stuck => simp [Comp.observeDeepWriter, found] at observed

theorem Comp.observeDeepWriter_mono
    {term : Comp} {fuel interface : Nat} {handler : AffineHandler}
    {result : List Val × Val}
    (observed : term.observeDeepWriter fuel interface handler = some result)
    (extra : Nat) :
    term.observeDeepWriter (fuel + extra) interface handler = some result := by
  induction extra with
  | zero => simpa using observed
  | succ extra ih =>
      rw [Nat.add_succ]
      exact Comp.observeDeepWriter_succ_of_some ih

structure DeepWriterPartialObservation (interface : Nat)
    (handler : AffineHandler) where
  observeAt : Nat → Option (List Val × Val)
  stable : ∀ {fuel result}, observeAt fuel = some result →
    observeAt (fuel + 1) = some result

def Comp.deepWriterApprox (term : Comp) (interface : Nat)
    (handler : AffineHandler) : DeepWriterPartialObservation interface handler where
  observeAt fuel := term.observeDeepWriter fuel interface handler
  stable := Comp.observeDeepWriter_succ_of_some

/-- Direct terminating operational semantics of the recursively reinstalled
handler. -/
inductive DeepWriterRuns (interface : Nat) (handler : AffineHandler) :
    Comp → List Val → Val → Prop where
  | returned : DeepWriterRuns interface handler (.ret value) [] value
  | internal : Step term next → DeepWriterRuns interface handler next log value →
      DeepWriterRuns interface handler term log value
  | tell : ExposesBase term request → request.operation = 0 →
      DeepWriterRuns interface handler (request.resume .unit) log value →
      DeepWriterRuns interface handler term (request.parameter :: log) value
  | matched : ExposesFree term request → request.interface = interface →
      handler.lookup request.operation = some clause →
      DeepWriterRuns interface handler (request.answerWith clause) log value →
      DeepWriterRuns interface handler term log value

theorem DeepWriterRuns.to_observation
    (runs : DeepWriterRuns interface handler term log value) :
    ∃ fuel, term.observeDeepWriter fuel interface handler = some (log, value) := by
  induction runs with
  | returned => exact ⟨1, rfl⟩
  | internal step runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      exact ⟨fuel + 1, by
        simp [Comp.observeDeepWriter, step.to_head, observed]⟩
  | tell exposed selected runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [exposed]
      simp [Comp.observeDeepWriter, BaseRequest.source_head, selected, observed]
  | matched exposed same found runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [exposed]
      simp [Comp.observeDeepWriter, FreeRequest.source_head, same, found, observed]

theorem Comp.observeDeepWriter_reflects
    (observed : term.observeDeepWriter fuel interface handler =
      some (log, value)) :
    DeepWriterRuns interface handler term log value := by
  induction fuel generalizing term log value with
  | zero => simp [Comp.observeDeepWriter] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned result =>
          simp [Comp.observeDeepWriter, found] at observed
          obtain ⟨rfl, rfl⟩ := observed
          have source := Comp.head_returned_sound found
          subst term
          exact .returned
      | internal next =>
          simp only [Comp.observeDeepWriter, found] at observed
          obtain ⟨step⟩ := Comp.head_internal_sound found
          exact .internal step (ih observed)
      | base request =>
          by_cases selected : request.operation = 0
          · simp only [Comp.observeDeepWriter, found, selected, if_pos,
              Option.map_eq_some_iff] at observed
            obtain ⟨tail, tailObserved, transformed⟩ := observed
            cases tail with
            | mk tailLog tailValue =>
                simp at transformed
                obtain ⟨rfl, rfl⟩ := transformed
                exact .tell (Comp.head_base_sound found) selected
                  (ih tailObserved)
          · simp [Comp.observeDeepWriter, found, selected] at observed
      | free request =>
          by_cases same : request.interface = interface
          · cases clauseFound : handler.lookup request.operation with
            | none =>
                simp [Comp.observeDeepWriter, found, same, clauseFound] at observed
            | some clause =>
                simp only [Comp.observeDeepWriter, found, same, if_pos,
                  clauseFound] at observed
                exact .matched (Comp.head_free_sound found) same clauseFound
                  (ih observed)
          · simp [Comp.observeDeepWriter, found, same] at observed
      | stuck => simp [Comp.observeDeepWriter, found] at observed

theorem deep_writer_finite_adequacy :
    DeepWriterRuns interface handler term log value ↔
      ∃ fuel, term.observeDeepWriter fuel interface handler =
        some (log, value) :=
  ⟨DeepWriterRuns.to_observation,
    fun ⟨_fuel, observed⟩ => Comp.observeDeepWriter_reflects observed⟩

/-- Union of all finite deep-handler approximants. -/
noncomputable def Comp.deepWriterLimit (term : Comp) (interface : Nat)
    (handler : AffineHandler) : Option (List Val × Val) := by
  classical
  by_cases existsObserved : ∃ fuel result,
      term.observeDeepWriter fuel interface handler = some result
  · exact some (Classical.choose (Classical.choose_spec existsObserved))
  · exact none

theorem Comp.deepWriterLimit_of_observed
    {term : Comp} {fuel interface : Nat} {handler : AffineHandler}
    {result : List Val × Val}
    (observed : term.observeDeepWriter fuel interface handler = some result) :
    term.deepWriterLimit interface handler = some result := by
  classical
  unfold Comp.deepWriterLimit
  split
  next existsObserved =>
    let chosenFuel := Classical.choose existsObserved
    let chosenResult := Classical.choose (Classical.choose_spec existsObserved)
    have chosenObserved :
        term.observeDeepWriter chosenFuel interface handler = some chosenResult :=
      Classical.choose_spec (Classical.choose_spec existsObserved)
    let common := Nat.max fuel chosenFuel
    have originalAtCommon := Comp.observeDeepWriter_mono observed
      (common - fuel)
    have chosenAtCommon := Comp.observeDeepWriter_mono chosenObserved
      (common - chosenFuel)
    have fuelEq : fuel + (common - fuel) = common :=
      Nat.add_sub_of_le (Nat.le_max_left fuel chosenFuel)
    have chosenFuelEq : chosenFuel + (common - chosenFuel) = common :=
      Nat.add_sub_of_le (Nat.le_max_right fuel chosenFuel)
    rw [fuelEq] at originalAtCommon
    rw [chosenFuelEq, originalAtCommon] at chosenAtCommon
    have equal : chosenResult = result :=
      (Option.some.inj chosenAtCommon).symm
    change some chosenResult = some result
    rw [equal]
  next absent => exact False.elim (absent ⟨fuel, result, observed⟩)

theorem Comp.deepWriterLimit_some_witness
    {term : Comp} {interface : Nat} {handler : AffineHandler}
    {result : List Val × Val}
    (observed : term.deepWriterLimit interface handler = some result) :
    ∃ fuel, term.observeDeepWriter fuel interface handler = some result := by
  classical
  unfold Comp.deepWriterLimit at observed
  split at observed
  next existsObserved =>
    let chosenFuel := Classical.choose existsObserved
    let chosenResult := Classical.choose (Classical.choose_spec existsObserved)
    have chosenObserved :
        term.observeDeepWriter chosenFuel interface handler = some chosenResult :=
      Classical.choose_spec (Classical.choose_spec existsObserved)
    have equal : chosenResult = result := Option.some.inj observed
    exact ⟨chosenFuel, by simpa [equal] using chosenObserved⟩
  next absent => cases observed

theorem deep_writer_limit_adequacy :
    DeepWriterRuns interface handler term log value ↔
      term.deepWriterLimit interface handler = some (log, value) := by
  constructor
  · intro runs
    obtain ⟨fuel, observed⟩ := runs.to_observation
    exact Comp.deepWriterLimit_of_observed observed
  · intro observed
    obtain ⟨fuel, finite⟩ := Comp.deepWriterLimit_some_witness observed
    exact Comp.observeDeepWriter_reflects finite

noncomputable def deepWriterLimitFamily (interface : Nat) (handler : AffineHandler) :
    DeepWriterApproximation :=
  fun term => term.deepWriterLimit interface handler

theorem iterateDeepWriter_le_limit (fuel interface : Nat)
    (handler : AffineHandler) :
    DeepWriterApproximation.LE (iterateDeepWriter interface handler fuel)
      (deepWriterLimitFamily interface handler) := by
  intro term result observed
  rw [← observeDeepWriter_eq_iterate fuel interface handler term] at observed
  exact Comp.deepWriterLimit_of_observed observed

theorem deepWriterFunctional_limit_witness
    (observed : deepWriterFunctional interface handler
      (deepWriterLimitFamily interface handler) term = some result) :
    ∃ fuel, deepWriterFunctional interface handler
      (iterateDeepWriter interface handler fuel) term = some result := by
  unfold deepWriterFunctional at observed ⊢
  cases found : term.head with
  | returned value => exact ⟨0, by simpa [found] using observed⟩
  | internal next =>
      simp only [found] at observed ⊢
      obtain ⟨fuel, finite⟩ := Comp.deepWriterLimit_some_witness observed
      exact ⟨fuel, by
        rwa [observeDeepWriter_eq_iterate fuel interface handler next] at finite⟩
  | base request =>
      by_cases selected : request.operation = 0
      · simp only [found, selected, if_pos, Option.map_eq_some_iff]
          at observed ⊢
        obtain ⟨tail, tailLimit, transformed⟩ := observed
        obtain ⟨fuel, tailFinite⟩ :=
          Comp.deepWriterLimit_some_witness tailLimit
        refine ⟨fuel, tail, ?_, transformed⟩
        rwa [observeDeepWriter_eq_iterate fuel interface handler
          (request.resume .unit)] at tailFinite
      · simp [found, selected] at observed
  | free request =>
      by_cases same : request.interface = interface
      · cases clauseFound : handler.lookup request.operation with
        | none => simp [found, same, clauseFound] at observed
        | some clause =>
            simp only [found, same, if_pos, clauseFound] at observed ⊢
            obtain ⟨fuel, finite⟩ := Comp.deepWriterLimit_some_witness observed
            exact ⟨fuel, by
              rwa [observeDeepWriter_eq_iterate fuel interface handler
                (request.answerWith clause)] at finite⟩
      · simp [found, same] at observed
  | stuck => simp [found] at observed

/-- Concrete fixed-point equation for the recursively reinstalled Writer
handler, obtained as the union of its finite shallow approximants. -/
theorem deepWriterLimit_unfold (interface : Nat) (handler : AffineHandler) :
    deepWriterFunctional interface handler
      (deepWriterLimitFamily interface handler) =
      deepWriterLimitFamily interface handler := by
  funext term
  apply Option.ext
  intro result
  constructor
  · intro functionalObserved
    obtain ⟨fuel, finite⟩ :=
      deepWriterFunctional_limit_witness functionalObserved
    have nextObserved : term.observeDeepWriter (fuel + 1) interface handler =
        some result := by
      rw [observeDeepWriter_eq_iterate]
      exact finite
    exact Comp.deepWriterLimit_of_observed nextObserved
  · intro limitObserved
    obtain ⟨fuel, finite⟩ := Comp.deepWriterLimit_some_witness limitObserved
    cases fuel with
    | zero => simp [Comp.observeDeepWriter] at finite
    | succ fuel =>
        rw [observeDeepWriter_eq_iterate] at finite
        exact deepWriterFunctional_monotone
          (iterateDeepWriter_le_limit fuel interface handler) _ _ finite

def twoTickTerm : Comp :=
  .letE (.freeOp 0 0 .unit)
    (.letE (.freeOp 0 0 .unit) (.ret .unit))

def recursiveTickHandler : AffineHandler :=
  ⟨[(0, .ret .unit)]⟩

theorem twoTickTerm_deep_observation :
    twoTickTerm.observeDeepWriter 7 0 recursiveTickHandler =
      some ([], .unit) := rfl

theorem silentLoop_deep_unobservable (fuel interface : Nat)
    (handler : AffineHandler) :
    silentLoop.observeDeepWriter fuel interface handler = none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

end EffectSemantics
