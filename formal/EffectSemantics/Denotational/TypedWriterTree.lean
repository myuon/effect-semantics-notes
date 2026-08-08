import EffectSemantics.Metatheory.HandlerPreservation

namespace EffectSemantics

/-- A closed syntactic value carrying kernel-checked evidence of its type. -/
structure ClosedVal (sig : Signature) (ty : Ty) where
  value : Val
  typing : HasVal sig [] value ty

/-- Response-type-indexed Writer/free tree.  Unlike the earlier raw behavior
tree, a free continuation can only be resumed with a closed value of the
response type declared by the signature. -/
inductive TypedWriterTree (sig : Signature) (α : Type) where
  | ret (value : α)
  | tell (message : Val) (next : TypedWriterTree sig α)
  | free (interface operation : Nat) {parameterTy responseTy : Ty}
      (lookup : sig.free interface operation =
        some ⟨parameterTy, responseTy⟩)
      (parameter : ClosedVal sig parameterTy)
      (continuation : ClosedVal sig responseTy → TypedWriterTree sig α)

namespace TypedWriterTree

def bind (tree : TypedWriterTree sig α)
    (next : α → TypedWriterTree sig β) : TypedWriterTree sig β :=
  match tree with
  | .ret value => next value
  | .tell message tail => .tell message (tail.bind next)
  | .free interface operation lookup parameter continuation =>
      .free interface operation lookup parameter (fun response =>
        (continuation response).bind next)

def map (function : α → β) (tree : TypedWriterTree sig α) :
    TypedWriterTree sig β :=
  tree.bind (fun value => .ret (function value))

theorem bind_ret (tree : TypedWriterTree sig α) :
    tree.bind ret = tree := by
  induction tree with
  | ret => rfl
  | tell message tail ih => simp [bind, ih]
  | free interface operation lookup parameter continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response

theorem bind_assoc (tree : TypedWriterTree sig α)
    (first : α → TypedWriterTree sig β)
    (second : β → TypedWriterTree sig γ) :
    (tree.bind first).bind second =
      tree.bind (fun value => (first value).bind second) := by
  induction tree with
  | ret => rfl
  | tell message tail ih => simp [bind, ih]
  | free interface operation lookup parameter continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response

theorem map_id (tree : TypedWriterTree sig α) : map id tree = tree := by
  simpa [map] using bind_ret tree

theorem map_comp (first : α → β) (second : β → γ)
    (tree : TypedWriterTree sig α) :
    map second (map first tree) = map (second ∘ first) tree := by
  rw [map, map, bind_assoc]
  rfl

/-- Ordered grading of the response-typed carrier. -/
inductive HasEffect : TypedWriterTree sig α → Effect → Type where
  | ret : HasEffect (.ret value) 1
  | tell : HasEffect tree effect →
      HasEffect (.tell message tree) ([EffectAtom.base 0] * effect)
  | free : (∀ response, HasEffect (continuation response) effect) →
      HasEffect (.free interface operation lookup parameter continuation)
        ([EffectAtom.free interface] * effect)
  | subeffect : HasEffect tree lower → lower ≤ upper → HasEffect tree upper

def HasEffect.weaken (typing : HasEffect tree lower) (bound : lower ≤ upper) :
    HasEffect tree upper := .subeffect typing bound

noncomputable def HasEffect.bind
    (treeTyping : HasEffect tree effect)
    (nextTyping : ∀ value, HasEffect (next value) nextEffect) :
    HasEffect (tree.bind next) (effect * nextEffect) := by
  induction treeTyping with
  | ret =>
      change HasEffect (next _) (1 * nextEffect)
      simpa using nextTyping _
  | tell tailTyping ih =>
      simpa only [TypedWriterTree.bind, Effect.mul_assoc] using
        HasEffect.tell ih
  | free continuationTyping ih =>
      simpa only [TypedWriterTree.bind, Effect.mul_assoc] using
        HasEffect.free ih
  | subeffect inner bound ih =>
      exact ih.weaken (Effect.le_seq bound (Effect.le_refl nextEffect))

inductive Observes : TypedWriterTree sig α → List Val → α → Type where
  | ret : Observes (.ret value) [] value
  | tell : Observes tree log value →
      Observes (.tell message tree) (message :: log) value

end TypedWriterTree
end EffectSemantics
