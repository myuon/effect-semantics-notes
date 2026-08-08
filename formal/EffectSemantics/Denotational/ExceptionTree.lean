import EffectSemantics.Denotational.WriterTree

namespace EffectSemantics

/-- Finite exception model: raising aborts the base computation, while free
requests retain resumptions. -/
inductive ExceptionTree (α : Type) where
  | ret (value : α)
  | raise (error : Val)
  | free (interface operation : Nat) (parameter : Val)
      (continuation : Val → ExceptionTree α)

namespace ExceptionTree

def bind (tree : ExceptionTree α)
    (next : α → ExceptionTree β) : ExceptionTree β :=
  match tree with
  | .ret value => next value
  | .raise error => .raise error
  | .free interface operation parameter continuation =>
      .free interface operation parameter (fun response =>
        (continuation response).bind next)

theorem bind_ret (tree : ExceptionTree α) : tree.bind ret = tree := by
  induction tree with
  | ret => rfl
  | raise => rfl
  | free interface operation parameter continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response

theorem bind_assoc (tree : ExceptionTree α)
    (first : α → ExceptionTree β) (second : β → ExceptionTree γ) :
    (tree.bind first).bind second =
      tree.bind (fun value => (first value).bind second) := by
  induction tree with
  | ret => rfl
  | raise => rfl
  | free interface operation parameter continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response

structure AffineSemantics where
  clause : Nat → Option (Val → ExceptionTree Val)

def shallow (selected : Nat) (handler : AffineSemantics) :
    ExceptionTree α → ExceptionTree α
  | .ret value => .ret value
  | .raise error => .raise error
  | .free interface operation parameter continuation =>
      if _same : interface = selected then
        match handler.clause operation with
        | some response => (response parameter).bind continuation
        | none => .free interface operation parameter (fun value =>
            shallow selected handler (continuation value))
      else
        .free interface operation parameter (fun value =>
          shallow selected handler (continuation value))

theorem shallow_match (found : handler.clause operation = some response) :
    shallow interface handler
      (.free interface operation parameter continuation) =
      (response parameter).bind continuation := by
  simp [shallow, found]

theorem shallow_forward_other (different : interface ≠ selected) :
    shallow selected handler
      (.free interface operation parameter continuation) =
      .free interface operation parameter (fun value =>
        shallow selected handler (continuation value)) := by
  simp [shallow, different]

theorem shallow_forward_missing (missing : handler.clause operation = none) :
    shallow interface handler
      (.free interface operation parameter continuation) =
      .free interface operation parameter (fun value =>
        shallow interface handler (continuation value)) := by
  simp [shallow, missing]

def runClosed : ExceptionTree α → Except Val α
  | .ret value => .ok value
  | .raise error => .error error
  | .free _ _ _ _ => .error .unit

inductive Rel (relation : α → β → Prop) :
    ExceptionTree α → ExceptionTree β → Prop where
  | ret : relation left right → Rel relation (.ret left) (.ret right)
  | raise : Rel relation (.raise error) (.raise error)
  | free : (∀ response, Rel relation (left response) (right response)) →
      Rel relation (.free interface operation parameter left)
        (.free interface operation parameter right)

theorem Rel.reflEq (tree : ExceptionTree α) : Rel (· = ·) tree tree := by
  induction tree with
  | ret value => exact .ret rfl
  | raise error => exact .raise
  | free interface operation parameter continuation ih => exact .free ih

theorem Rel.bind (treeRelation : Rel relation left right)
    (nextRelation : ∀ {a b}, relation a b →
      Rel resultRelation (leftNext a) (rightNext b)) :
    Rel resultRelation (left.bind leftNext) (right.bind rightNext) := by
  induction treeRelation with
  | ret related => exact nextRelation related
  | raise => exact .raise
  | free related ih => exact .free ih

theorem Rel.shallow (treeRelation : Rel relation left right)
    (selected : Nat) (handler : AffineSemantics) :
    Rel relation (ExceptionTree.shallow selected handler left)
      (ExceptionTree.shallow selected handler right) := by
  induction treeRelation with
  | ret related => exact .ret related
  | raise => exact .raise
  | free related ih =>
      rename_i leftContinuation rightContinuation interface operation parameter
      by_cases same : interface = selected
      · subst selected
        cases found : handler.clause operation with
        | none =>
            rw [shallow_forward_missing found, shallow_forward_missing found]
            exact .free ih
        | some response =>
            rw [shallow_match found, shallow_match found]
            apply Rel.bind (Rel.reflEq (response parameter))
            intro a b equal
            subst b
            exact related a
      · rw [shallow_forward_other same, shallow_forward_other same]
        exact .free ih

end ExceptionTree
end EffectSemantics
