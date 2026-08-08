import EffectSemantics.Syntax.HandlerTyping

namespace EffectSemantics.Examples

open EffectSemantics

def tickHandler : AffineHandler :=
  ⟨[(0, .ret .unit)]⟩

@[simp] theorem tickHandler_finds_tick :
    tickHandler.lookup 0 = some (.ret .unit) := by
  rfl

@[simp] theorem tickHandler_misses_tock :
    tickHandler.lookup 1 = none := by
  rfl

@[simp] theorem subst0_ret_unit (parameter : Val) :
    (Comp.ret Val.unit).subst0 parameter = .ret .unit := rfl

/-- A matching request installs the response clause before the bare source
continuation and removes the shallow handler. -/
def tick_matches :
    ShallowStep
      (.shallow 0 tickHandler (.freeOp 0 0 .unit))
      (.core (.letE (.ret .unit) (.ret (.var 0)))) := by
  have step := ShallowStep.matched
    (request := FreeRequest.mk 0 0 .unit [])
    (handler := tickHandler) (clause := .ret .unit)
    (term := .freeOp 0 0 .unit) (interface := 0)
    (by rfl) (by rfl) (by rfl)
  simpa [FreeRequest.answerWith, FreeRequest.openResume,
    EvalContext.rename] using step

/-- A missing same-interface clause is a forwarding boundary. -/
def tock_forwards :
    ShallowBoundary
      (.shallow 0 tickHandler (.freeOp 0 1 .unit)) := by
  apply ShallowBoundary.freeMissing
    (request := ⟨0, 1, .unit, []⟩)
  · rfl
  · rfl

@[simp] theorem tock_resume_reinstalls (response : Val) :
    tock_forwards.resume response =
      .shallow 0 tickHandler (.ret response) := rfl

end EffectSemantics.Examples
