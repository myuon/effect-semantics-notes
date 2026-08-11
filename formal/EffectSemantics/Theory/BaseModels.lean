import EffectSemantics.Denotational.StateTree
import EffectSemantics.Denotational.ExceptionTree

namespace EffectSemantics

/-- A lawful monad structure shared by the concrete base models. -/
structure MonadStructure (carrier : Type → Type) where
  pure : ∀ {α}, α → carrier α
  bind : ∀ {α β}, carrier α → (α → carrier β) → carrier β
  leftUnit : ∀ {α β} (value : α) (next : α → carrier β),
    bind (pure value) next = next value
  rightUnit : ∀ {α} (tree : carrier α), bind tree pure = tree
  associative : ∀ {α β γ} (tree : carrier α)
      (first : α → carrier β) (second : β → carrier γ),
    bind (bind tree first) second =
      bind tree (fun value => bind (first value) second)

def writerMonad : MonadStructure WriterTree where
  pure := WriterTree.ret
  bind := WriterTree.bind
  leftUnit := fun _ _ => rfl
  rightUnit := WriterTree.bind_ret
  associative := WriterTree.bind_assoc

def stateMonad : MonadStructure StateTree where
  pure := StateTree.ret
  bind := StateTree.bind
  leftUnit := fun _ _ => rfl
  rightUnit := StateTree.bind_ret
  associative := StateTree.bind_assoc

def exceptionMonad : MonadStructure ExceptionTree where
  pure := ExceptionTree.ret
  bind := ExceptionTree.bind
  leftUnit := fun _ _ => rfl
  rightUnit := ExceptionTree.bind_ret
  associative := ExceptionTree.bind_assoc

end EffectSemantics
