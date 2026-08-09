import EffectSemantics.Operational.LanguageWriterAdequacy

namespace EffectSemantics.LanguageWriterTree

structure AffineSemantics (sig : LanguageSignature) where
  clause : ∀ (interface operation : Nat)
      {parameterTy responseTy : LanguageTy}
      (_lookup : sig.free interface operation =
        some ⟨parameterTy, responseTy⟩),
    Option (LanguageClosedVal sig parameterTy →
      LanguageWriterTree sig (LanguageClosedVal sig responseTy))

/-- Direct affine shallow interpretation.  Writer and unrelated free nodes
are traversed until the first matching selected request.  A match runs the
clause and feeds its response to the bare continuation, ending this handler. -/
noncomputable def shallow (selected : Nat) (handler : AffineSemantics sig) :
    LanguageWriterTree sig α → LanguageWriterTree sig α
  | .ret value => .ret value
  | .tell message tail => .tell message (shallow selected handler tail)
  | .free interface operation lookup parameter continuation =>
      if _same : interface = selected then
        match handler.clause interface operation lookup with
        | some response => (response parameter).bind continuation
        | none => .free interface operation lookup parameter
            (fun value => shallow selected handler (continuation value))
      else .free interface operation lookup parameter
        (fun value => shallow selected handler (continuation value))

theorem shallow_return (value : α) :
    shallow selected handler (.ret value) = .ret value := rfl

theorem shallow_tell (message : FinLanguageVal)
    (tail : LanguageWriterTree sig α) :
    shallow selected handler (.tell message tail) =
      .tell message (shallow selected handler tail) := rfl

theorem shallow_forward_other
    (different : interface ≠ selected) :
    shallow selected handler
      (.free interface operation lookup parameter continuation) =
      .free interface operation lookup parameter
        (fun response => shallow selected handler (continuation response)) := by
  simp [shallow, different]

theorem shallow_match
    (found : handler.clause selected operation lookup = some response) :
    shallow selected handler
      (.free selected operation lookup parameter continuation) =
      (response parameter).bind continuation := by
  simp [shallow, found]

theorem shallow_forward_missing
    (missing : handler.clause selected operation lookup = none) :
    shallow selected handler
      (.free selected operation lookup parameter continuation) =
      .free selected operation lookup parameter
        (fun response => shallow selected handler (continuation response)) := by
  simp [shallow, missing]

theorem shallow_map (function : α → β) (tree : LanguageWriterTree sig α) :
    map function (shallow selected handler tree) =
      shallow selected handler (map function tree) := by
  induction tree with
  | ret => rfl
  | tell message tail ih =>
      exact congrArg (LanguageWriterTree.tell message) ih
  | free interface operation lookup parameter continuation ih =>
      by_cases same : interface = selected
      · subst selected
        cases found : handler.clause interface operation lookup with
        | none =>
            rw [shallow_forward_missing found]
            simp only [map, bind]
            rw [shallow_forward_missing found]
            congr
            funext response
            exact ih response
        | some response =>
            rw [shallow_match found]
            simp only [map, bind_assoc, bind]
            rw [shallow_match found]
      · rw [shallow_forward_other same]
        simp only [map, bind]
        rw [shallow_forward_other same]
        congr
        funext response
        exact ih response

theorem Rel.reflEq (tree : LanguageWriterTree sig α) :
    Rel (· = ·) tree tree := by
  induction tree with
  | ret => exact .ret rfl
  | tell message tail ih => exact .tell ih
  | free interface operation lookup parameter continuation ih => exact .free ih

theorem Rel.shallow
    {sig : LanguageSignature} {α β : Type} {relation : α → β → Prop}
    {left : LanguageWriterTree sig α} {right : LanguageWriterTree sig β}
    (treeRelation : Rel relation left right)
    (selected : Nat) (handler : AffineSemantics sig) :
    Rel relation (shallow selected handler left)
      (shallow selected handler right) := by
  induction treeRelation with
  | ret related => exact .ret related
  | tell related ih => exact .tell ih
  | free related ih =>
      rename_i responseTy leftContinuation rightContinuation interface operation
        parameterTy lookup parameter
      by_cases same : interface = selected
      · subst selected
        cases found : handler.clause interface operation lookup with
        | none =>
            rw [shallow_forward_missing found, shallow_forward_missing found]
            exact .free ih
        | some response =>
            rw [shallow_match found, shallow_match found]
            apply Rel.bind
              (relation := fun left right => left = right)
              (Rel.reflEq (response parameter))
            intro leftValue rightValue equal
            subst rightValue
            exact related leftValue
      · rw [shallow_forward_other same, shallow_forward_other same]
        exact .free ih

end EffectSemantics.LanguageWriterTree
