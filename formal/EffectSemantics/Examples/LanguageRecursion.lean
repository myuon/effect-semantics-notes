import EffectSemantics.Metatheory.LanguagePreservation

namespace EffectSemantics

open EffectLanguage

def unitFreeLanguageSignature : LanguageSignature where
  base _ := none
  free interface operation :=
    if interface = 0 ∧ operation = 0 then
      some ⟨.unit, .unit⟩
    else none

theorem unitFreeLanguageSignature_lookup :
    unitFreeLanguageSignature.free 0 0 = some ⟨.unit, .unit⟩ := by
  simp [unitFreeLanguageSignature]

def loopAtom : EffectAtom := .free 0

def loopLanguage : EffectLanguage := star (principal [loopAtom])

/-- Under `[argument, self]`, perform the free operation and then call self.
The response introduced by `letE` shifts self to de Bruijn index two. -/
def effectfulLoopBody : RecLanguageComp :=
  .letE (.freeOp 0 0 .unit) (.app (.var 2) .unit)

def effectfulLoopBodyTyping :
    HasLanguageComp (mode := .recursive) unitFreeLanguageSignature
      [.unit, .arr .unit loopLanguage .unit]
      effectfulLoopBody .unit loopLanguage := by
  have request : HasLanguageComp (mode := .recursive) unitFreeLanguageSignature
      [.unit, .arr .unit loopLanguage .unit]
      (.freeOp 0 0 .unit) .unit (principal [loopAtom]) :=
    .freeOp unitFreeLanguageSignature_lookup .unit
  have recurse : HasLanguageComp (mode := .recursive) unitFreeLanguageSignature
      [.unit, .unit, .arr .unit loopLanguage .unit]
      (.app (.var 2) .unit) .unit loopLanguage :=
    .app (.var rfl) .unit
  exact .subeffect (.letE request recurse)
    (by
      change EffectLanguage.seq (principal [loopAtom]) loopLanguage ≤ loopLanguage
      exact EffectLanguage.seq_star_le_star _)

def effectfulLoop : RecLanguageVal :=
  .fixLam .recursive .unit loopLanguage effectfulLoopBody

def effectfulLoopTyping :
    HasLanguageVal (mode := .recursive) unitFreeLanguageSignature [] effectfulLoop
      (.arr .unit loopLanguage .unit) :=
  .fixLam .recursive effectfulLoopBodyTyping

def runEffectfulLoop : RecLanguageComp := .app effectfulLoop .unit

def runEffectfulLoopTyping :
    HasLanguageComp (mode := .recursive) unitFreeLanguageSignature [] runEffectfulLoop
      .unit loopLanguage :=
  .app effectfulLoopTyping .unit

def runEffectfulLoop_unfolds :
    LanguageStep runEffectfulLoop
      (effectfulLoopBody.subst2 .unit effectfulLoop) :=
  .fixBeta

/-- The actual recursive beta step, not only its abstract effect skeleton,
preserves the regular latent grade. -/
def runEffectfulLoop_unfoldedTyping :
    HasLanguageComp (mode := .recursive) unitFreeLanguageSignature []
      (effectfulLoopBody.subst2 .unit effectfulLoop) .unit loopLanguage :=
  runEffectfulLoop_unfolds.preserve runEffectfulLoopTyping

/-- A conditional recursive body.  The false branch returns immediately and
the true branch performs one request and recurs; union gives it a natural
conditional may-effect without forcing both branches to an exact word. -/
def conditionalLoopBody : RecLanguageComp :=
  .ite (.var 0)
    (.letE (.freeOp 0 0 .unit) (.app (.var 2) (.var 1)))
    (.ret .unit)

def conditionalLoopBodyTyping :
    HasLanguageComp (mode := .recursive) unitFreeLanguageSignature
      [.bool, .arr .bool loopLanguage .unit]
      conditionalLoopBody .unit loopLanguage := by
  have thenTyping : HasLanguageComp (mode := .recursive) unitFreeLanguageSignature
      [.bool, .arr .bool loopLanguage .unit]
      (.letE (.freeOp 0 0 .unit) (.app (.var 2) (.var 1)))
      .unit loopLanguage := by
    -- The loop body only uses its argument structurally; changing Unit to
    -- Bool therefore leaves the same de Bruijn derivation.
    have request : HasLanguageComp (mode := .recursive) unitFreeLanguageSignature
        [.bool, .arr .bool loopLanguage .unit]
        (.freeOp 0 0 .unit) .unit (principal [loopAtom]) :=
      .freeOp unitFreeLanguageSignature_lookup .unit
    have recurse : HasLanguageComp (mode := .recursive) unitFreeLanguageSignature
        [.unit, .bool, .arr .bool loopLanguage .unit]
        (.app (.var 2) (.var 1)) .unit loopLanguage :=
      .app (.var rfl) (.var rfl)
    -- Use the Bool argument for the recursive call in this variant.
    exact .subeffect (.letE request recurse)
      (EffectLanguage.seq_star_le_star _)
  exact .subeffect (.ite (.var rfl) thenTyping (.ret .unit))
    (EffectLanguage.join_le (EffectLanguage.le_refl _)
      (EffectLanguage.one_le_star _))

end EffectSemantics
