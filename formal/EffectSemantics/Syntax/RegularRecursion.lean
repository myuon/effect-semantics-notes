import EffectSemantics.Certificate.RegularRecursion

namespace EffectSemantics

open EffectLanguage

/-- A small, explicit language of effect skeletons.  It isolates the grading
issue of recursive calls from value typing: `self` denotes one call to the
function currently being checked. -/
inductive RecursiveEffectExpr where
  | pure
  | atom (label : EffectAtom)
  | seq (first second : RecursiveEffectExpr)
  | self
  deriving DecidableEq, Repr

namespace RecursiveEffectExpr

/-- Interpret a body under a proposed latent grade for recursive calls. -/
def grade (selfGrade : EffectLanguage) : RecursiveEffectExpr → EffectLanguage
  | .pure => principal 1
  | .atom label => principal [label]
  | .seq first second =>
      EffectLanguage.seq (grade selfGrade first) (grade selfGrade second)
  | .self => selfGrade

/-- A recursive effect skeleton is typable at `latent` when one unfolding,
with recursive calls assumed to have that same latent grade, stays below it. -/
def HasRecursiveGrade (body : RecursiveEffectExpr)
    (latent : EffectLanguage) : Prop :=
  grade latent body ≤ latent

def prefixLoop (head : RecursiveEffectExpr) : RecursiveEffectExpr :=
  .seq head .self

@[simp] theorem grade_prefixLoop (head : RecursiveEffectExpr)
    (latent : EffectLanguage) :
    grade latent (prefixLoop head) =
      EffectLanguage.seq (grade latent head) latent := rfl

/-- Syntactic predicate selecting genuinely nonrecursive prefixes. -/
def SelfFree : RecursiveEffectExpr → Prop
  | .pure | .atom _ => True
  | .seq first second => first.SelfFree ∧ second.SelfFree
  | .self => False

theorem grade_selfFree_independent (free : body.SelfFree) :
    grade left body = grade right body := by
  induction body with
  | pure => rfl
  | atom => rfl
  | seq first second firstIH secondIH =>
      simp only [SelfFree] at free
      simp only [grade]
      rw [firstIH free.1, secondIH free.2]
  | self => exact False.elim free

/-- Correct version of the prefix-loop rule, exposing its necessary
nonrecursive-prefix hypothesis. -/
theorem selfFree_prefixLoop_typable (free : head.SelfFree) :
    HasRecursiveGrade (prefixLoop head)
      (star (grade (principal 1) head)) := by
  change EffectLanguage.seq
    (grade (star (grade (principal 1) head)) head)
    (star (grade (principal 1) head)) ≤
      star (grade (principal 1) head)
  rw [grade_selfFree_independent free]
  exact seq_star_le_star _

def operationLoop (label : EffectAtom) : RecursiveEffectExpr :=
  prefixLoop (.atom label)

theorem operationLoop_typable (label : EffectAtom) :
    HasRecursiveGrade (operationLoop label)
      (star (principal [label])) :=
  selfFree_prefixLoop_typable (head := .atom label) trivial

/-- Reassigning the same operation loop a principal finite-word latent grade
would require exactly the impossible absorption inequality. -/
theorem operationLoop_not_finitely_typable
    (label : EffectAtom) (latent : Effect) :
    ¬ HasRecursiveGrade (operationLoop label) (principal latent) := by
  intro typing
  exact Effect.not_cons_le_self label latent
    (EffectLanguage.le_of_principal_le (by
      simpa [HasRecursiveGrade, operationLoop, prefixLoop, grade,
        principal_seq] using typing))

end RecursiveEffectExpr
end EffectSemantics
