import EffectSemantics.Denotational.WriterTree

namespace EffectSemantics

/-- Finite Boolean-state model with user-defined free requests. -/
inductive StateTree (α : Type) where
  | ret (value : α)
  | get (continuation : Bool → StateTree α)
  | put (state : Bool) (next : StateTree α)
  | free (interface operation : Nat) (parameter : Val)
      (continuation : Val → StateTree α)

namespace StateTree

def bind (tree : StateTree α) (next : α → StateTree β) : StateTree β :=
  match tree with
  | .ret value => next value
  | .get continuation => .get (fun state => (continuation state).bind next)
  | .put state tail => .put state (tail.bind next)
  | .free interface operation parameter continuation =>
      .free interface operation parameter (fun response =>
        (continuation response).bind next)

def map (function : α → β) (tree : StateTree α) : StateTree β :=
  tree.bind (fun value => .ret (function value))

theorem bind_ret (tree : StateTree α) : tree.bind ret = tree := by
  induction tree with
  | ret => rfl
  | get continuation ih =>
      simp only [bind]
      congr
      funext state
      exact ih state
  | put state tail ih => simp [bind, ih]
  | free interface operation parameter continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response

theorem bind_assoc (tree : StateTree α) (first : α → StateTree β)
    (second : β → StateTree γ) :
    (tree.bind first).bind second =
      tree.bind (fun value => (first value).bind second) := by
  induction tree with
  | ret => rfl
  | get continuation ih =>
      simp only [bind]
      congr
      funext state
      exact ih state
  | put state tail ih => simp [bind, ih]
  | free interface operation parameter continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response

structure AffineSemantics where
  clause : Nat → Option (Val → StateTree Val)

def shallow (selected : Nat) (handler : AffineSemantics) :
    StateTree α → StateTree α
  | .ret value => .ret value
  | .get continuation => .get (fun state =>
      shallow selected handler (continuation state))
  | .put state next => .put state (shallow selected handler next)
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

def runClosed : StateTree α → Bool → Option (α × Bool)
  | .ret value, state => some (value, state)
  | .get continuation, state => runClosed (continuation state) state
  | .put newState next, _ => runClosed next newState
  | .free _ _ _ _, _ => none

inductive Rel (relation : α → β → Prop) : StateTree α → StateTree β → Prop where
  | ret : relation left right → Rel relation (.ret left) (.ret right)
  | get : (∀ state, Rel relation (left state) (right state)) →
      Rel relation (.get left) (.get right)
  | put : Rel relation left right →
      Rel relation (.put state left) (.put state right)
  | free : (∀ response, Rel relation (left response) (right response)) →
      Rel relation (.free interface operation parameter left)
        (.free interface operation parameter right)

theorem Rel.reflEq (tree : StateTree α) : Rel (· = ·) tree tree := by
  induction tree with
  | ret value => exact .ret rfl
  | get continuation ih => exact .get ih
  | put state next ih => exact .put ih
  | free interface operation parameter continuation ih => exact .free ih

theorem Rel.bind (treeRelation : Rel relation left right)
    (nextRelation : ∀ {a b}, relation a b →
      Rel resultRelation (leftNext a) (rightNext b)) :
    Rel resultRelation (left.bind leftNext) (right.bind rightNext) := by
  induction treeRelation with
  | ret related => exact nextRelation related
  | get related ih => exact .get ih
  | put related ih => exact .put ih
  | free related ih => exact .free ih

theorem Rel.shallow (treeRelation : Rel relation left right)
    (selected : Nat) (handler : AffineSemantics) :
    Rel relation (StateTree.shallow selected handler left)
      (StateTree.shallow selected handler right) := by
  induction treeRelation with
  | ret related => exact .ret related
  | get related ih => exact .get ih
  | put related ih => exact .put ih
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

end StateTree
end EffectSemantics
