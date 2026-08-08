import EffectSemantics.Recursive.TypedDeepWriter
import EffectSemantics.Recursive.StableObservation

namespace EffectSemantics

inductive DeepWriterBoundary where
  | returned (log : List Val) (value : Val)
  | base (log : List Val) (request : BaseRequest)
  | free (log : List Val) (request : FreeRequest)
  deriving DecidableEq

def DeepWriterBoundary.prepend (entry : Val) :
    DeepWriterBoundary → DeepWriterBoundary
  | .returned log value => .returned (entry :: log) value
  | .base log request => .base (entry :: log) request
  | .free log request => .free (entry :: log) request

/-- Finite boundary semantics for the derived deep Writer handler.  Unlike
the closed observer, nonselected and genuinely unhandled requests are exposed
to the surrounding program. -/
def Comp.observeDeepWriterBoundary : Nat → Nat → AffineHandler → Comp →
    Option DeepWriterBoundary
  | 0, _, _, _ => none
  | fuel + 1, interface, handler, term =>
      match term.head with
      | .returned value => some (.returned [] value)
      | .internal next => next.observeDeepWriterBoundary fuel interface handler
      | .base request =>
          if request.operation = 0 then
            ((request.resume .unit).observeDeepWriterBoundary fuel interface handler).map
              (DeepWriterBoundary.prepend request.parameter)
          else some (.base [] request)
      | .free request =>
          if request.interface = interface then
            match handler.lookup request.operation with
            | some clause =>
                (request.answerWith clause).observeDeepWriterBoundary
                  fuel interface handler
            | none => some (.free [] request)
          else some (.free [] request)
      | .stuck => none

theorem Comp.observeDeepWriterBoundary_succ_of_some
    {term : Comp} {fuel interface : Nat} {handler : AffineHandler}
    {boundary : DeepWriterBoundary}
    (observed : term.observeDeepWriterBoundary fuel interface handler =
      some boundary) :
    term.observeDeepWriterBoundary (fuel + 1) interface handler =
      some boundary := by
  induction fuel generalizing term boundary with
  | zero => simp [Comp.observeDeepWriterBoundary] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value =>
          simpa [Comp.observeDeepWriterBoundary, found] using observed
      | internal next =>
          simp only [Comp.observeDeepWriterBoundary, found] at observed ⊢
          exact ih observed
      | base request =>
          by_cases selected : request.operation = 0
          · simp only [Comp.observeDeepWriterBoundary, found, selected, if_pos,
              Option.map_eq_some_iff] at observed ⊢
            obtain ⟨tail, tailObserved, transformed⟩ := observed
            exact ⟨tail, ih tailObserved, transformed⟩
          · simpa [Comp.observeDeepWriterBoundary, found, selected] using observed
      | free request =>
          by_cases same : request.interface = interface
          · cases clauseFound : handler.lookup request.operation with
            | none =>
                simpa [Comp.observeDeepWriterBoundary, found, same, clauseFound]
                  using observed
            | some clause =>
                simp only [Comp.observeDeepWriterBoundary, found, same, if_pos,
                  clauseFound] at observed ⊢
                exact ih observed
          · simpa [Comp.observeDeepWriterBoundary, found, same] using observed
      | stuck => simp [Comp.observeDeepWriterBoundary, found] at observed

theorem Comp.observeDeepWriterBoundary_mono
    {term : Comp} {fuel interface : Nat} {handler : AffineHandler}
    {boundary : DeepWriterBoundary}
    (observed : term.observeDeepWriterBoundary fuel interface handler =
      some boundary) (extra : Nat) :
    term.observeDeepWriterBoundary (fuel + extra) interface handler =
      some boundary := by
  induction extra with
  | zero => simpa using observed
  | succ extra ih =>
      rw [Nat.add_succ]
      exact Comp.observeDeepWriterBoundary_succ_of_some ih

abbrev DeepWriterBoundaryObservation (_interface : Nat)
    (_handler : AffineHandler) := StableObservation DeepWriterBoundary

def Comp.deepWriterBoundaryApprox (term : Comp) (interface : Nat)
    (handler : AffineHandler) : DeepWriterBoundaryObservation interface handler where
  observeAt fuel := term.observeDeepWriterBoundary fuel interface handler
  stable := Comp.observeDeepWriterBoundary_succ_of_some

noncomputable def Comp.deepWriterBoundaryLimit (term : Comp)
    (interface : Nat) (handler : AffineHandler) : Option DeepWriterBoundary := by
  classical
  by_cases existsObserved : ∃ fuel boundary,
      term.observeDeepWriterBoundary fuel interface handler = some boundary
  · exact some (Classical.choose (Classical.choose_spec existsObserved))
  · exact none

theorem Comp.deepWriterBoundaryLimit_of_observed
    {term : Comp} {fuel interface : Nat} {handler : AffineHandler}
    {boundary : DeepWriterBoundary}
    (observed : term.observeDeepWriterBoundary fuel interface handler =
      some boundary) :
    term.deepWriterBoundaryLimit interface handler = some boundary := by
  classical
  unfold Comp.deepWriterBoundaryLimit
  split
  next existsObserved =>
    let chosenFuel := Classical.choose existsObserved
    let chosenBoundary := Classical.choose (Classical.choose_spec existsObserved)
    have chosenObserved :
        term.observeDeepWriterBoundary chosenFuel interface handler =
          some chosenBoundary :=
      Classical.choose_spec (Classical.choose_spec existsObserved)
    let common := Nat.max fuel chosenFuel
    have originalStable :
        term.observeDeepWriterBoundary common interface handler = some boundary := by
      obtain ⟨extra, equal⟩ := Nat.le.dest (Nat.le_max_left fuel chosenFuel)
      change term.observeDeepWriterBoundary (Nat.max fuel chosenFuel)
        interface handler = some boundary
      simpa [equal] using Comp.observeDeepWriterBoundary_mono observed extra
    have chosenStable :
        term.observeDeepWriterBoundary common interface handler =
          some chosenBoundary := by
      obtain ⟨extra, equal⟩ := Nat.le.dest (Nat.le_max_right fuel chosenFuel)
      change term.observeDeepWriterBoundary (Nat.max fuel chosenFuel)
        interface handler = some chosenBoundary
      simpa [equal] using
        Comp.observeDeepWriterBoundary_mono chosenObserved extra
    have equal : chosenBoundary = boundary := by
      rw [originalStable] at chosenStable
      exact (Option.some.inj chosenStable).symm
    change some chosenBoundary = some boundary
    rw [equal]
  next absent => exact False.elim (absent ⟨fuel, boundary, observed⟩)

theorem Comp.deepWriterBoundaryLimit_some_witness
    {term : Comp} {interface : Nat} {handler : AffineHandler}
    {boundary : DeepWriterBoundary}
    (observed : term.deepWriterBoundaryLimit interface handler = some boundary) :
    ∃ fuel, term.observeDeepWriterBoundary fuel interface handler =
      some boundary := by
  classical
  unfold Comp.deepWriterBoundaryLimit at observed
  split at observed
  next existsObserved =>
    let chosenFuel := Classical.choose existsObserved
    let chosenBoundary := Classical.choose (Classical.choose_spec existsObserved)
    have chosenObserved :
        term.observeDeepWriterBoundary chosenFuel interface handler =
          some chosenBoundary :=
      Classical.choose_spec (Classical.choose_spec existsObserved)
    have equal : chosenBoundary = boundary := Option.some.inj observed
    exact ⟨chosenFuel, by simpa [equal] using chosenObserved⟩
  next absent => cases observed

/-- Exhaustive typed deep handling discharges the selected interface from
every finite outward free boundary. -/
theorem observeDeepWriterBoundary_discharges
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (exhaustive : handler.Exhaustive sig interface)
    (writerUnit : WriterResponseUnit sig)
    (observed : term.observeDeepWriterBoundary fuel interface handler =
      some (.free log request)) :
    request.interface ≠ interface := by
  induction fuel generalizing term effect log request with
  | zero => simp [Comp.observeDeepWriterBoundary] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value => simp [Comp.observeDeepWriterBoundary, found] at observed
      | internal next =>
          simp only [Comp.observeDeepWriterBoundary, found] at observed
          obtain ⟨step⟩ := Comp.head_internal_sound found
          exact ih (step.preserve typing) observed
      | base baseRequest =>
          by_cases selected : baseRequest.operation = 0
          · simp only [Comp.observeDeepWriterBoundary, found, selected, if_pos,
              Option.map_eq_some_iff] at observed
            obtain ⟨tail, tailObserved, transformed⟩ := observed
            have exposed := Comp.head_base_sound found
            rw [exposed] at typing
            cases tail with
            | returned tailLog value => cases transformed
            | base tailLog outward => cases transformed
            | free tailLog outward =>
                cases transformed
                let requestTyping := typing.exposedBaseView
                have responseEq : requestTyping.responseTy = .unit := by
                  apply writerUnit requestTyping.parameterTy requestTyping.responseTy
                  simpa [selected] using requestTyping.lookup
                have unitTyping : HasVal sig [] .unit requestTyping.responseTy := by
                  rw [responseEq]
                  exact .unit
                exact ih (requestTyping.resumeTyping unitTyping) tailObserved
          · simp [Comp.observeDeepWriterBoundary, found, selected] at observed
      | free freeRequest =>
          by_cases same : freeRequest.interface = interface
          · cases clauseFound : handler.lookup freeRequest.operation with
            | some clause =>
                simp only [Comp.observeDeepWriterBoundary, found, same, if_pos,
                  clauseFound] at observed
                have exposed := Comp.head_free_sound found
                rw [exposed] at typing
                exact ih (handlerTyping.answerWithTyping typing same clauseFound)
                  observed
            | none =>
                have exposed := Comp.head_free_sound found
                rw [exposed] at typing
                have requestTyping := typing.exposedFreeView
                obtain ⟨clause, clauseExists⟩ := exhaustive freeRequest.operation
                  requestTyping.parameterTy requestTyping.responseTy (by
                    simpa [same] using requestTyping.lookup)
                rw [clauseFound] at clauseExists
                cases clauseExists
          · simp [Comp.observeDeepWriterBoundary, found, same] at observed
            have equal : freeRequest = request := by
              exact observed.2
            subst request
            exact same
      | stuck => simp [Comp.observeDeepWriterBoundary, found] at observed

theorem deepWriterBoundaryLimit_discharges
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (exhaustive : handler.Exhaustive sig interface)
    (writerUnit : WriterResponseUnit sig)
    (observed : term.deepWriterBoundaryLimit interface handler =
      some (.free log request)) :
    request.interface ≠ interface := by
  obtain ⟨fuel, finite⟩ := Comp.deepWriterBoundaryLimit_some_witness observed
  exact observeDeepWriterBoundary_discharges typing handlerTyping exhaustive
    writerUnit finite

end EffectSemantics
