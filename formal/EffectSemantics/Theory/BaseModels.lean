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

/-- A monad relator with bind closure, abstracting the common
structural proof used by Writer, State and Exception. -/
structure MonadRelator (carrier : Type → Type)
    (monad : MonadStructure carrier) where
  Rel : ∀ {α β}, (α → β → Prop) → carrier α → carrier β → Prop
  reflEq : ∀ {α} (tree : carrier α), Rel (· = ·) tree tree
  bindClosed : ∀ {α β γ δ} {valueRel : α → β → Prop}
      {resultRel : γ → δ → Prop} {left : carrier α} {right : carrier β}
      {leftNext : α → carrier γ} {rightNext : β → carrier δ},
    Rel valueRel left right →
    (∀ {a b}, valueRel a b → Rel resultRel (leftNext a) (rightNext b)) →
    Rel resultRel (monad.bind left leftNext) (monad.bind right rightNext)

structure ShallowRelator (carrier : Type → Type) (handler : Type)
    (monad : MonadStructure carrier) (relator : MonadRelator carrier monad) where
  shallow : ∀ {α}, Nat → handler → carrier α → carrier α
  preserves : ∀ {α β} {relation : α → β → Prop}
      {left : carrier α} {right : carrier β},
    relator.Rel relation left right → ∀ selected clauses,
    relator.Rel relation (shallow selected clauses left)
      (shallow selected clauses right)

def writerMonad : MonadStructure WriterTree where
  pure := WriterTree.ret
  bind := WriterTree.bind
  leftUnit := fun _ _ => rfl
  rightUnit := WriterTree.bind_ret
  associative := WriterTree.bind_assoc

def writerRelator : MonadRelator WriterTree writerMonad where
  Rel := WriterTree.Rel
  reflEq := WriterTree.Rel.reflEq
  bindClosed := WriterTree.Rel.bind

def writerShallowRelator :
    ShallowRelator WriterTree WriterTree.AffineSemantics
      writerMonad writerRelator where
  shallow := WriterTree.shallow
  preserves := fun related selected clauses => related.shallow selected clauses

def stateMonad : MonadStructure StateTree where
  pure := StateTree.ret
  bind := StateTree.bind
  leftUnit := fun _ _ => rfl
  rightUnit := StateTree.bind_ret
  associative := StateTree.bind_assoc

def stateRelator : MonadRelator StateTree stateMonad where
  Rel := StateTree.Rel
  reflEq := StateTree.Rel.reflEq
  bindClosed := StateTree.Rel.bind

def stateShallowRelator :
    ShallowRelator StateTree StateTree.AffineSemantics
      stateMonad stateRelator where
  shallow := StateTree.shallow
  preserves := fun related selected clauses => related.shallow selected clauses

def exceptionMonad : MonadStructure ExceptionTree where
  pure := ExceptionTree.ret
  bind := ExceptionTree.bind
  leftUnit := fun _ _ => rfl
  rightUnit := ExceptionTree.bind_ret
  associative := ExceptionTree.bind_assoc

def exceptionRelator :
    MonadRelator ExceptionTree exceptionMonad where
  Rel := ExceptionTree.Rel
  reflEq := ExceptionTree.Rel.reflEq
  bindClosed := ExceptionTree.Rel.bind

def exceptionShallowRelator :
    ShallowRelator ExceptionTree ExceptionTree.AffineSemantics
      exceptionMonad exceptionRelator where
  shallow := ExceptionTree.shallow
  preserves := fun related selected clauses => related.shallow selected clauses

end EffectSemantics
