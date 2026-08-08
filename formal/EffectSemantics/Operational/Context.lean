import EffectSemantics.Syntax.RenameSubst

namespace EffectSemantics

/-- In the fine-grain core only the bound computation of `let` is evaluated.
Other eliminators already receive values. -/
inductive Frame where
  | letE (body : Comp)
  deriving DecidableEq, Repr

abbrev EvalContext := List Frame

def Frame.plug (frame : Frame) (term : Comp) : Comp :=
  match frame with
  | .letE body => .letE term body

/-- Frames are stored innermost first. -/
def EvalContext.plug : EvalContext → Comp → Comp
  | [], term => term
  | frame :: rest, term => EvalContext.plug rest (frame.plug term)

@[simp] theorem EvalContext.plug_nil (term : Comp) :
    EvalContext.plug [] term = term := rfl

@[simp] theorem EvalContext.plug_cons (frame : Frame) (rest : EvalContext)
    (term : Comp) :
    EvalContext.plug (frame :: rest) term =
      EvalContext.plug rest (frame.plug term) := rfl

theorem EvalContext.plug_append (inner outer : EvalContext) (term : Comp) :
    EvalContext.plug (inner ++ outer) term =
      EvalContext.plug outer (EvalContext.plug inner term) := by
  induction inner generalizing term with
  | nil => rfl
  | cons frame rest ih =>
      simp only [List.cons_append, plug_cons]
      exact ih (frame.plug term)

end EffectSemantics
