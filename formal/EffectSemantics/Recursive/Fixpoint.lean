import EffectSemantics.Metatheory.Progress

namespace EffectSemantics

/-- The recursive-function value used by the operational unfolding rule. -/
def recursiveSelf (domain : Ty) (latent : Effect) (body : Comp) : Val :=
  .fixLam domain latent body

def recursive_application_unfolds
    (domain : Ty) (latent : Effect) (body : Comp) (argument : Val) :
    Step (.app (recursiveSelf domain latent body) argument)
      (body.subst2 argument (recursiveSelf domain latent body)) :=
  .fixBeta

/-- A closed silent loop.  It witnesses that an empty may-effect does not imply
termination once recursive functions are present. -/
def silentLoopBody : Comp := .app (.var 1) (.var 0)

def silentLoop : Comp :=
  .app (.fixLam .unit 1 silentLoopBody) .unit

def emptySignature : Signature where
  base _ := none
  free _ _ := none

def silentLoopBodyTyping :
    HasComp emptySignature
      [.unit, .arr .unit 1 .unit] silentLoopBody .unit 1 := by
  exact .app (.var rfl) (.var rfl)

def silentLoopTyping :
    HasComp emptySignature [] silentLoop .unit 1 := by
  exact .app (.fixLam silentLoopBodyTyping) .unit

/-- One unfolding returns syntactically to the same closed computation. -/
def silentLoop_step : Step silentLoop silentLoop := by
  apply Step.fixBeta

def silentLoop_preservation :
    HasComp emptySignature [] silentLoop .unit 1 :=
  silentLoop_step.preserve silentLoopTyping

def silentLoop_progress : Progress silentLoop :=
  silentLoopTyping.progressClosed

/-- An infinite internal reduction witness. -/
structure Diverges (term : Comp) where
  trace : Nat → Comp
  starts : trace 0 = term
  advances : ∀ index, Step (trace index) (trace (index + 1))

def silentLoop_diverges : Diverges silentLoop where
  trace _ := silentLoop
  starts := rfl
  advances _ := silentLoop_step

end EffectSemantics
