import EffectSemantics.Denotational.WriterTT

namespace EffectSemantics.WriterTree

/-- Ordered may-effect indexing of the concrete Writer/free carrier. -/
inductive HasEffect : WriterTree α → Effect → Type where
  | ret : HasEffect (.ret value) 1
  | tell : HasEffect tree effect →
      HasEffect (.tell message tree) ([EffectAtom.base 0] * effect)
  | free : (∀ response, HasEffect (continuation response) effect) →
      HasEffect (.free interface operation parameter continuation)
        ([EffectAtom.free interface] * effect)
  | subeffect : HasEffect tree lower → lower ≤ upper → HasEffect tree upper

def HasEffect.weaken (typing : HasEffect tree lower) (bound : lower ≤ upper) :
    HasEffect tree upper := .subeffect typing bound

/-- Graded bind for the concrete carrier. -/
noncomputable def HasEffect.bind
    (treeTyping : HasEffect tree effect)
    (nextTyping : ∀ value, HasEffect (next value) nextEffect) :
    HasEffect (tree.bind next) (effect * nextEffect) := by
  induction treeTyping with
  | ret => simpa using nextTyping _
  | tell tailTyping ih =>
      simpa only [WriterTree.tell_bind, Effect.mul_assoc] using
        HasEffect.tell ih
  | free continuationTyping ih =>
      simpa only [WriterTree.free_bind, Effect.mul_assoc] using
        HasEffect.free ih
  | subeffect inner bound ih =>
      exact ih.weaken
        (Effect.le_seq bound (Effect.le_refl nextEffect))

noncomputable def HasEffect.map
    {α β : Type} {tree : WriterTree α} {effect : Effect}
    (treeTyping : HasEffect tree effect) (function : α → β) :
    HasEffect (WriterTree.map function tree) effect := by
  change HasEffect (tree.bind (fun value => .ret (function value))) effect
  have mapped := treeTyping.bind (next := fun value => .ret (function value))
    (nextEffect := 1) (fun _ => HasEffect.ret)
  simpa only [Effect.mul_one] using mapped

def writerTrace (log : List Val) : Effect :=
  log.map (fun _ => EffectAtom.base 0)

/-- Every concrete Writer observation occurs in order inside its declared
effect upper bound. -/
theorem HasEffect.observationBound
    (typing : HasEffect tree effect)
    (observes : Observes tree log value) : writerTrace log ≤ effect := by
  induction typing generalizing log value with
  | ret =>
      cases observes
      exact Effect.le_refl 1
  | tell tailTyping ih =>
      cases observes with
      | tell tailObserved =>
          exact List.Sublist.cons_cons _ (ih tailObserved)
  | free continuationTyping ih => cases observes
  | subeffect inner bound ih =>
      exact Effect.le_trans (ih observes) bound

end EffectSemantics.WriterTree
