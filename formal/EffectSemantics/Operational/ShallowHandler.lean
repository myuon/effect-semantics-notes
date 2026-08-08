import EffectSemantics.Syntax.AffineHandler

namespace EffectSemantics

def Frame.rename (rename : Nat → Nat) : Frame → Frame
  | .letE body => .letE (body.rename (liftRen rename))

def EvalContext.rename (rename : Nat → Nat) (context : EvalContext) : EvalContext :=
  context.map (Frame.rename rename)

/-- The captured continuation opened underneath a fresh response binder.
Variables from the surrounding source term are shifted; variable zero is the
response produced by the affine clause. -/
def FreeRequest.openResume (request : FreeRequest) : Comp :=
  (request.context.rename (· + 1)).plug (.ret (.var 0))

/-- Installing the affine response in front of the bare continuation. -/
def FreeRequest.answerWith (request : FreeRequest) (clause : Comp) : Comp :=
  .letE (clause.subst0 request.parameter) request.openResume

/-- Internal and matching transitions of an affine shallow handler. -/
inductive ShallowStep : HandlerState → HandlerState → Type where
  | internal : Step term next →
      ShallowStep (.shallow interface handler term)
        (.shallow interface handler next)
  | returned :
      ShallowStep (.shallow interface handler (.ret value)) (.core (.ret value))
  | matched : ExposesFree term request → request.interface = interface →
      handler.lookup request.operation = some clause →
      ShallowStep (.shallow interface handler term)
        (.core (request.answerWith clause))

/-- An unhandled boundary is forwarded, with the pending shallow handler
reinstalled only around the continuation supplied by the environment. -/
inductive ShallowBoundary : HandlerState → Type where
  | base (request : BaseRequest) :
      ShallowBoundary (.shallow interface handler request.source)
  | freeOther (request : FreeRequest)
      (different : request.interface ≠ interface) :
      ShallowBoundary (.shallow interface handler request.source)
  | freeMissing (request : FreeRequest)
      (same : request.interface = interface)
      (missing : handler.lookup request.operation = none) :
      ShallowBoundary (.shallow interface handler request.source)

def ShallowBoundary.resume :
    ShallowBoundary (.shallow interface handler term) → Val → HandlerState
  | .base request, response =>
      .shallow interface handler (request.resume response)
  | .freeOther request _, response =>
      .shallow interface handler (request.resume response)
  | .freeMissing request _ _, response =>
      .shallow interface handler (request.resume response)

def ShallowStep.matchConstructed
    (exposed : ExposesFree term request)
    (same : request.interface = interface)
    (found : handler.lookup request.operation = some clause) :
    ShallowStep (.shallow interface handler term)
      (.core (request.answerWith clause)) :=
  .matched exposed same found

@[simp] theorem FreeRequest.answerWith_empty
    (interface operation : Nat) (parameter : Val) (clause : Comp) :
    (FreeRequest.mk interface operation parameter []).answerWith clause =
      .letE (clause.subst0 parameter) (.ret (.var 0)) := rfl

end EffectSemantics
