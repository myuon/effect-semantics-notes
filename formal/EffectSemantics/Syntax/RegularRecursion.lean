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
  | choice (left right : RecursiveEffectExpr)
  | self
  deriving DecidableEq, Repr

namespace RecursiveEffectExpr

/-- Interpret a body under a proposed latent grade for recursive calls. -/
def grade (selfGrade : EffectLanguage) : RecursiveEffectExpr → EffectLanguage
  | .pure => principal 1
  | .atom label => principal [label]
  | .seq first second =>
      EffectLanguage.seq (grade selfGrade first) (grade selfGrade second)
  | .choice left right =>
      EffectLanguage.join (grade selfGrade left) (grade selfGrade right)
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
  | .choice left right => left.SelfFree ∧ right.SelfFree
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
  | choice left right leftIH rightIH =>
      simp only [SelfFree] at free
      simp only [grade]
      rw [leftIH free.1, rightIH free.2]
  | self => exact False.elim free

/-- Effect expressions are positive in the assumed recursive-call grade. -/
theorem grade_mono (bound : lower ≤ upper) :
    grade lower body ≤ grade upper body := by
  induction body generalizing lower upper with
  | pure => exact EffectLanguage.le_refl _
  | atom => exact EffectLanguage.le_refl _
  | seq first second firstIH secondIH =>
      exact EffectLanguage.seq_mono
        (firstIH (lower := lower) (upper := upper) bound)
        (secondIH (lower := lower) (upper := upper) bound)
  | choice left right leftIH rightIH =>
      exact EffectLanguage.join_mono
        (leftIH (lower := lower) (upper := upper) bound)
        (rightIH (lower := lower) (upper := upper) bound)
  | self => exact bound

/-- Add the zero-unfolding possibility to the behavior of one body
unfolding.  Its least fixed point records every finite effect prefix generated
by arbitrary branching and any finite number of recursive calls. -/
def closureFunctional (body : RecursiveEffectExpr)
    (candidate : EffectLanguage) : EffectLanguage :=
  EffectLanguage.join (principal 1) (grade candidate body)

theorem closureFunctional_mono (bound : lower ≤ upper) :
    closureFunctional body lower ≤ closureFunctional body upper :=
  EffectLanguage.join_mono (EffectLanguage.le_refl _) (grade_mono bound)

def recursiveGrade (body : RecursiveEffectExpr) : EffectLanguage :=
  EffectLanguage.leastPrefixed (closureFunctional body)

theorem recursiveGrade_unfold (body : RecursiveEffectExpr) :
    closureFunctional body (recursiveGrade body) = recursiveGrade body :=
  EffectLanguage.leastPrefixed_fixed
    (fun {left right} bound =>
      closureFunctional_mono (body := body) (lower := left) (upper := right) bound)

theorem recursiveGrade_pure (body : RecursiveEffectExpr) :
    principal 1 ≤ recursiveGrade body := by
  have whole : closureFunctional body (recursiveGrade body) ≤
      recursiveGrade body := by
    rw [recursiveGrade_unfold body]
    exact EffectLanguage.le_refl _
  exact EffectLanguage.le_trans
    (EffectLanguage.le_join_left (principal 1)
      (grade (recursiveGrade body) body)) whole

theorem recursiveGrade_body (body : RecursiveEffectExpr) :
    grade (recursiveGrade body) body ≤ recursiveGrade body := by
  have whole : closureFunctional body (recursiveGrade body) ≤
      recursiveGrade body := by
    rw [recursiveGrade_unfold body]
    exact EffectLanguage.le_refl _
  exact EffectLanguage.le_trans
    (EffectLanguage.le_join_right (principal 1)
      (grade (recursiveGrade body) body)) whole

/-- Every recursive effect expression, including branches and several self
calls, has a canonical well-formed latent grade. -/
theorem recursiveGrade_types (body : RecursiveEffectExpr) :
    HasRecursiveGrade body (recursiveGrade body) :=
  recursiveGrade_body body

theorem recursiveGrade_least
    (pureBound : principal 1 ≤ candidate)
    (bodyBound : grade candidate body ≤ candidate) :
    recursiveGrade body ≤ candidate := by
  apply EffectLanguage.leastPrefixed_le
  exact EffectLanguage.join_le pureBound bodyBound

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

/-- The generic least-grade construction agrees with the earlier explicit
Kleene-star solution on the one-operation loop. -/
theorem recursiveGrade_operationLoop (label : EffectAtom) :
    recursiveGrade (operationLoop label) = star (principal [label]) := by
  apply EffectLanguage.le_antisymm
  · apply recursiveGrade_least
    · exact EffectLanguage.one_le_star _
    · simpa [operationLoop, prefixLoop, grade] using
        EffectLanguage.seq_star_le_star (principal [label])
  · apply EffectLanguage.star_le_of_prefixed
    · exact recursiveGrade_pure _
    · simpa [operationLoop, prefixLoop, grade] using
        recursiveGrade_body (operationLoop label)

/-- A branch may either return immediately or emit and recur. -/
def optionalOperationLoop (label : EffectAtom) : RecursiveEffectExpr :=
  .choice .pure (.seq (.atom label) .self)

theorem optionalOperationLoop_typable (label : EffectAtom) :
    HasRecursiveGrade (optionalOperationLoop label)
      (recursiveGrade (optionalOperationLoop label)) :=
  recursiveGrade_types _

/-- A body with two recursive calls on one branch.  The generic construction
does not rely on affinity of `self`; it assigns the least closed may-effect
language to this nonlinear skeleton as well. -/
def doubleSelfBody (label : EffectAtom) : RecursiveEffectExpr :=
  .choice (.seq (.atom label) .self)
    (.seq (.atom label) (.seq .self .self))

theorem doubleSelfBody_typable (label : EffectAtom) :
    HasRecursiveGrade (doubleSelfBody label)
      (recursiveGrade (doubleSelfBody label)) :=
  recursiveGrade_types _

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
