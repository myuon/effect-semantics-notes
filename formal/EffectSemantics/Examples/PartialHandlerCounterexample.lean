import EffectSemantics.Examples.GenericBaseInstances

namespace EffectSemantics

def partialUserHandler :
    FreeExtension.AffineHandler writerBaseSignature userOperationSignature where
  clause request :=
    if request.operation = 0 then some (.ret .unit) else none

def missingUserRequest : UserOperation :=
  ⟨0, 1, .unit⟩

def missingUserTree :
    FreeExtension writerBaseSignature userOperationSignature Val :=
  .freeOp missingUserRequest (fun _ => .ret .unit)

@[simp] theorem partialUserHandler_missing :
    partialUserHandler.clause missingUserRequest = none := by
  rfl

/-- A partial handler cannot eliminate its interface at interface-level
granularity: a missing operation is forwarded as the outer node.  Reinstalling
the handler in recursive continuations cannot change this first boundary. -/
theorem partial_handler_missing_clause_forwards :
    FreeExtension.shallow partialUserHandler missingUserTree =
      .freeOp missingUserRequest (fun _ =>
        FreeExtension.shallow partialUserHandler (.ret (.unit : Val))) := by
  exact FreeExtension.shallow_forward partialUserHandler
    partialUserHandler_missing

theorem partial_handler_does_not_eliminate_interface :
    ∃ continuation,
      FreeExtension.shallow partialUserHandler missingUserTree =
        FreeExtension.freeOp missingUserRequest continuation := by
  exact ⟨fun response =>
    FreeExtension.shallow partialUserHandler (.ret (.unit : Val)),
    partial_handler_missing_clause_forwards⟩

end EffectSemantics
