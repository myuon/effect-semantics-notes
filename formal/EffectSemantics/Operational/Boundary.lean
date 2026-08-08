import EffectSemantics.Operational.Step

namespace EffectSemantics

/-- Data exposed by an unhandled source operation.  The source operation has
no continuation argument; `context` is reconstructed by the CBV machine. -/
structure FreeRequest where
  interface : Nat
  operation : Nat
  parameter : Val
  context : EvalContext
  deriving DecidableEq, Repr

def FreeRequest.source (request : FreeRequest) : Comp :=
  request.context.plug (.freeOp request.interface request.operation request.parameter)

def FreeRequest.resume (request : FreeRequest) (response : Val) : Comp :=
  request.context.plug (.ret response)

def ExposesFree (term : Comp) (request : FreeRequest) : Prop :=
  term = request.source

structure BaseRequest where
  operation : Nat
  parameter : Val
  context : EvalContext
  deriving DecidableEq, Repr

def BaseRequest.source (request : BaseRequest) : Comp :=
  request.context.plug (.baseOp request.operation request.parameter)

def BaseRequest.resume (request : BaseRequest) (response : Val) : Comp :=
  request.context.plug (.ret response)

def ExposesBase (term : Comp) (request : BaseRequest) : Prop :=
  term = request.source

theorem free_operation_has_no_source_continuation
    (interface operation : Nat) (parameter : Val) :
    (FreeRequest.mk interface operation parameter []).source =
      .freeOp interface operation parameter := rfl

end EffectSemantics
