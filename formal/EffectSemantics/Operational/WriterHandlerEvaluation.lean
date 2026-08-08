import EffectSemantics.Operational.WriterEvaluation
import EffectSemantics.Operational.ShallowHandler

namespace EffectSemantics

def BaseRequest.underLet (request : BaseRequest) (body : Comp) : BaseRequest :=
  { request with context := request.context ++ [.letE body] }

def FreeRequest.underLet (request : FreeRequest) (body : Comp) : FreeRequest :=
  { request with context := request.context ++ [.letE body] }

@[simp] theorem BaseRequest.underLet_source
    (request : BaseRequest) (body : Comp) :
    (request.underLet body).source = .letE request.source body := by
  simp [BaseRequest.underLet, BaseRequest.source, EvalContext.plug_append,
    Frame.plug]

@[simp] theorem BaseRequest.underLet_resume
    (request : BaseRequest) (body : Comp) (response : Val) :
    (request.underLet body).resume response =
      .letE (request.resume response) body := by
  simp [BaseRequest.underLet, BaseRequest.resume, EvalContext.plug_append,
    Frame.plug]

@[simp] theorem FreeRequest.underLet_source
    (request : FreeRequest) (body : Comp) :
    (request.underLet body).source = .letE request.source body := by
  simp [FreeRequest.underLet, FreeRequest.source, EvalContext.plug_append,
    Frame.plug]

@[simp] theorem FreeRequest.underLet_resume
    (request : FreeRequest) (body : Comp) (response : Val) :
    (request.underLet body).resume response =
      .letE (request.resume response) body := by
  simp [FreeRequest.underLet, FreeRequest.resume, EvalContext.plug_append,
    Frame.plug]

/-- The operational behavior tree of CBV sequencing is semantic tree bind. -/
theorem ProducesWriterTree.letE
    (boundProduces : ProducesWriterTree bound tree)
    (bodyProduces : ∀ value,
      ProducesWriterTree (body.subst0 value) (continuation value)) :
    ProducesWriterTree (.letE bound body) (tree.bind continuation) := by
  induction boundProduces with
  | returned =>
      exact .internal .letReturn (bodyProduces _)
  | internal step produces ih =>
      exact .internal (.underLet step) ih
  | @tell term request tail exposed selected produces ih =>
      apply ProducesWriterTree.tell
        (request := request.underLet body)
      · show .letE term body = (request.underLet body).source
        rw [exposed, BaseRequest.underLet_source]
      · exact selected
      · simpa using ih
  | @free term request requestContinuation exposed produces ih =>
      apply ProducesWriterTree.free
        (request := request.underLet body)
        (continuation := fun response =>
          (requestContinuation response).bind continuation)
      · show .letE term body = (request.underLet body).source
        rw [exposed, FreeRequest.underLet_source]
      · intro response
        simpa using ih response

/-- A semantic clause family implements the source handler when every source
clause produces the corresponding response tree and absence agrees. -/
structure ModelsWriterHandler (handler : AffineHandler)
    (semantics : WriterTree.AffineSemantics) : Prop where
  present : ∀ {operation clause}, handler.lookup operation = some clause →
    ∃ response, semantics.clause operation = some response ∧
      ∀ parameter, ProducesWriterTree (clause.subst0 parameter)
        (response parameter)
  absent : ∀ {operation}, handler.lookup operation = none →
    semantics.clause operation = none

/-- Direct big-step behavior of one shallow source handler.  Matching executes
the clause and bare continuation outside the handler; every forwarded request
reinstalls the handler only around the resumed continuation. -/
inductive HandlesWriterTree (interface : Nat) (handler : AffineHandler) :
    Comp → WriterTree Val → Prop where
  | returned : HandlesWriterTree interface handler (.ret value) (.ret value)
  | internal : Step term next → HandlesWriterTree interface handler next tree →
      HandlesWriterTree interface handler term tree
  | tell : ExposesBase term request → request.operation = 0 →
      HandlesWriterTree interface handler (request.resume .unit) tail →
      HandlesWriterTree interface handler term (.tell request.parameter tail)
  | freeOther : ExposesFree term request → request.interface ≠ interface →
      (∀ response, HandlesWriterTree interface handler
        (request.resume response) (continuation response)) →
      HandlesWriterTree interface handler term
        (.free request.interface request.operation request.parameter continuation)
  | freeMissing : ExposesFree term request → request.interface = interface →
      handler.lookup request.operation = none →
      (∀ response, HandlesWriterTree interface handler
        (request.resume response) (continuation response)) →
      HandlesWriterTree interface handler term
        (.free request.interface request.operation request.parameter continuation)
  | matched : ExposesFree term request → request.interface = interface →
      handler.lookup request.operation = some clause →
      ProducesWriterTree (request.answerWith clause) tree →
      HandlesWriterTree interface handler term tree

/-- Source-level shallow evaluation commutes with the structural Writer-tree
handler.  This is the untyped operational core of handler adequacy. -/
theorem ProducesWriterTree.shallow
    (models : ModelsWriterHandler handler semantics)
    (produces : ProducesWriterTree term tree) :
    HandlesWriterTree interface handler term
      (WriterTree.shallow interface semantics tree) := by
  induction produces with
  | returned => exact .returned
  | internal step produces ih => exact .internal step ih
  | tell exposed selected produces ih =>
      exact .tell exposed selected ih
  | @free term request continuation exposed produces ih =>
      by_cases same : request.interface = interface
      · subst interface
        cases found : handler.lookup request.operation with
        | none =>
            rw [WriterTree.shallow_forward_missing (models.absent found)]
            exact .freeMissing exposed rfl found ih
        | some clause =>
            obtain ⟨response, semanticFound, clauseProduces⟩ := models.present found
            rw [WriterTree.shallow_match semantics semanticFound]
            apply HandlesWriterTree.matched exposed rfl found
            exact ProducesWriterTree.letE (clauseProduces request.parameter)
              (fun value => by simpa using produces value)
      · rw [WriterTree.shallow_forward_other same]
        exact .freeOther exposed same ih

end EffectSemantics
