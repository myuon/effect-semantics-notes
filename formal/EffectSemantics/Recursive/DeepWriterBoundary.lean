import EffectSemantics.Recursive.TypedDeepWriter

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

end EffectSemantics
