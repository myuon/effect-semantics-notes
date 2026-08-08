import EffectSemantics.Recursive.DeepWriterContinuity

namespace EffectSemantics

abbrev DeepResultApproximation := Comp → Option Val

def eraseWriterApproximation (source : DeepWriterApproximation) :
    DeepResultApproximation := fun term => (source term).map Prod.snd

def deepResultFunctional (interface : Nat) (handler : AffineHandler)
    (next : DeepResultApproximation) : DeepResultApproximation := fun term =>
  match term.head with
  | .returned value => some value
  | .internal term' => next term'
  | .base request =>
      if request.operation = 0 then next (request.resume .unit) else none
  | .free request =>
      if request.interface = interface then
        match handler.lookup request.operation with
        | some clause => next (request.answerWith clause)
        | none => none
      else none
  | .stuck => none

/-- Concrete nonidentity one-layer morphism: forgetting the Writer log
commutes with recursive handler unfolding. -/
theorem eraseWriterApproximation_commutes
    (source : DeepWriterApproximation) :
    eraseWriterApproximation
      (deepWriterFunctional interface handler source) =
    deepResultFunctional interface handler
      (eraseWriterApproximation source) := by
  funext term
  unfold eraseWriterApproximation deepWriterFunctional deepResultFunctional
  cases found : term.head with
  | returned value => simp
  | internal next => simp
  | base request =>
      by_cases selected : request.operation = 0 <;>
        simp [selected, Function.comp_def]
  | free request =>
      by_cases same : request.interface = interface
      · cases clauseFound : handler.lookup request.operation <;>
          simp [same, clauseFound]
      · simp [same]
  | stuck => simp

def iterateDeepResult (interface : Nat) (handler : AffineHandler) :
    Nat → DeepResultApproximation
  | 0 => fun _ => none
  | fuel + 1 => deepResultFunctional interface handler
      (iterateDeepResult interface handler fuel)

theorem erase_iterateDeepWriter (fuel interface : Nat)
    (handler : AffineHandler) :
    eraseWriterApproximation (iterateDeepWriter interface handler fuel) =
      iterateDeepResult interface handler fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [iterateDeepWriter, iterateDeepResult,
        eraseWriterApproximation_commutes, ih]

noncomputable def Comp.deepResultLimit (term : Comp) (interface : Nat)
    (handler : AffineHandler) : Option Val :=
  (term.deepWriterLimit interface handler).map Prod.snd

noncomputable def deepResultLimitFamily (interface : Nat)
    (handler : AffineHandler) : DeepResultApproximation :=
  fun term => term.deepResultLimit interface handler

theorem erase_deepWriterLimitFamily (interface : Nat)
    (handler : AffineHandler) :
    eraseWriterApproximation (deepWriterLimitFamily interface handler) =
      deepResultLimitFamily interface handler := rfl

/-- Log erasure transports the recursive Writer fixed point to a fixed point
of the result-only functional. -/
theorem deepResultLimit_unfold (interface : Nat) (handler : AffineHandler) :
    deepResultFunctional interface handler
      (deepResultLimitFamily interface handler) =
      deepResultLimitFamily interface handler := by
  rw [← erase_deepWriterLimitFamily]
  rw [← eraseWriterApproximation_commutes]
  rw [deepWriterLimit_unfold]

theorem deepResultLimit_of_writer
    {term : Comp} {interface : Nat} {handler : AffineHandler}
    {log : List Val} {value : Val}
    (observed : term.deepWriterLimit interface handler = some (log, value)) :
    term.deepResultLimit interface handler = some value := by
  simp [Comp.deepResultLimit, observed]

end EffectSemantics
