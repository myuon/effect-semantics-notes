import EffectSemantics.Examples.WriterShallow

namespace EffectSemantics

def iterate (step : α → α) : Nat → α → α
  | 0, value => value
  | fuel + 1, value => iterate step fuel (step value)

@[simp] theorem iterate_zero (step : α → α) (value : α) :
    iterate step 0 value = value := rfl

@[simp] theorem iterate_succ (step : α → α) (fuel : Nat) (value : α) :
    iterate step (fuel + 1) value = iterate step fuel (step value) := rfl

theorem iterate_add (step : α → α) (first second : Nat) (value : α) :
    iterate step (first + second) value =
      iterate step first (iterate step second value) := by
  induction second generalizing value with
  | zero => simp
  | succ second ih =>
      rw [Nat.add_succ, iterate_succ, iterate_succ, ih]

namespace WriterTree

/-- Finite approximants to the deep handler derived by repeatedly applying the
direct shallow handler. -/
def deepApprox (fuel : Nat) (selected : Nat) (handler : AffineSemantics)
    (tree : WriterTree α) : WriterTree α :=
  iterate (shallow selected handler) fuel tree

@[simp] theorem deepApprox_zero :
    deepApprox 0 selected handler tree = tree := rfl

@[simp] theorem deepApprox_succ :
    deepApprox (fuel + 1) selected handler tree =
      deepApprox fuel selected handler (shallow selected handler tree) := rfl

theorem deepApprox_add :
    deepApprox (first + second) selected handler tree =
      deepApprox first selected handler
        (deepApprox second selected handler tree) :=
  iterate_add _ _ _ _

theorem deepApprox_fixed
    (fixed : shallow selected handler tree = tree) :
    deepApprox fuel selected handler tree = tree := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [deepApprox_succ, fixed, ih]

theorem Rel.deepApprox (treeRelation : Rel relation left right)
    (fuel : Nat) (selected : Nat) (handler : AffineSemantics) :
    Rel relation (deepApprox fuel selected handler left)
      (deepApprox fuel selected handler right) := by
  induction fuel generalizing left right with
  | zero => exact treeRelation
  | succ fuel ih =>
      exact ih (treeRelation.shallow selected handler)

theorem deepApprox_map (function : α → β) :
    map function (deepApprox fuel selected handler tree) =
      deepApprox fuel selected handler (map function tree) := by
  induction fuel generalizing tree with
  | zero => rfl
  | succ fuel ih =>
      rw [deepApprox_succ, deepApprox_succ, ih, shallow_map]

end WriterTree
end EffectSemantics
