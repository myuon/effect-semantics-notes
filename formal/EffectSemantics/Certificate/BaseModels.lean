import EffectSemantics.Denotational.StateTree
import EffectSemantics.Denotational.ExceptionTree

namespace EffectSemantics

/-- Minimal finite monad certificate shared by the concrete base models. -/
structure FiniteMonadCert (carrier : Type → Type) where
  pure : ∀ {α}, α → carrier α
  bind : ∀ {α β}, carrier α → (α → carrier β) → carrier β
  leftUnit : ∀ {α β} (value : α) (next : α → carrier β),
    bind (pure value) next = next value
  rightUnit : ∀ {α} (tree : carrier α), bind tree pure = tree
  associative : ∀ {α β γ} (tree : carrier α)
      (first : α → carrier β) (second : β → carrier γ),
    bind (bind tree first) second =
      bind tree (fun value => bind (first value) second)

/-- Relator and bind-closure certificate, abstracting exactly the common
structural proof used by Writer, State and Exception. -/
structure FiniteRelatorCert (carrier : Type → Type)
    (monad : FiniteMonadCert carrier) where
  Rel : ∀ {α β}, (α → β → Prop) → carrier α → carrier β → Prop
  reflEq : ∀ {α} (tree : carrier α), Rel (· = ·) tree tree
  bindClosed : ∀ {α β γ δ} {valueRel : α → β → Prop}
      {resultRel : γ → δ → Prop} {left : carrier α} {right : carrier β}
      {leftNext : α → carrier γ} {rightNext : β → carrier δ},
    Rel valueRel left right →
    (∀ {a b}, valueRel a b → Rel resultRel (leftNext a) (rightNext b)) →
    Rel resultRel (monad.bind left leftNext) (monad.bind right rightNext)

structure FiniteShallowRelatorCert (carrier : Type → Type) (handler : Type)
    (monad : FiniteMonadCert carrier) (relator : FiniteRelatorCert carrier monad) where
  shallow : ∀ {α}, Nat → handler → carrier α → carrier α
  preserves : ∀ {α β} {relation : α → β → Prop}
      {left : carrier α} {right : carrier β},
    relator.Rel relation left right → ∀ selected clauses,
    relator.Rel relation (shallow selected clauses left)
      (shallow selected clauses right)

def writerMonadCert : FiniteMonadCert WriterTree where
  pure := WriterTree.ret
  bind := WriterTree.bind
  leftUnit := fun _ _ => rfl
  rightUnit := WriterTree.bind_ret
  associative := WriterTree.bind_assoc

def writerRelatorCert : FiniteRelatorCert WriterTree writerMonadCert where
  Rel := WriterTree.Rel
  reflEq := WriterTree.Rel.reflEq
  bindClosed := WriterTree.Rel.bind

def writerShallowRelatorCert :
    FiniteShallowRelatorCert WriterTree WriterTree.AffineSemantics
      writerMonadCert writerRelatorCert where
  shallow := WriterTree.shallow
  preserves := fun related selected clauses => related.shallow selected clauses

def stateMonadCert : FiniteMonadCert StateTree where
  pure := StateTree.ret
  bind := StateTree.bind
  leftUnit := fun _ _ => rfl
  rightUnit := StateTree.bind_ret
  associative := StateTree.bind_assoc

def stateRelatorCert : FiniteRelatorCert StateTree stateMonadCert where
  Rel := StateTree.Rel
  reflEq := StateTree.Rel.reflEq
  bindClosed := StateTree.Rel.bind

def stateShallowRelatorCert :
    FiniteShallowRelatorCert StateTree StateTree.AffineSemantics
      stateMonadCert stateRelatorCert where
  shallow := StateTree.shallow
  preserves := fun related selected clauses => related.shallow selected clauses

def exceptionMonadCert : FiniteMonadCert ExceptionTree where
  pure := ExceptionTree.ret
  bind := ExceptionTree.bind
  leftUnit := fun _ _ => rfl
  rightUnit := ExceptionTree.bind_ret
  associative := ExceptionTree.bind_assoc

def exceptionRelatorCert :
    FiniteRelatorCert ExceptionTree exceptionMonadCert where
  Rel := ExceptionTree.Rel
  reflEq := ExceptionTree.Rel.reflEq
  bindClosed := ExceptionTree.Rel.bind

def exceptionShallowRelatorCert :
    FiniteShallowRelatorCert ExceptionTree ExceptionTree.AffineSemantics
      exceptionMonadCert exceptionRelatorCert where
  shallow := ExceptionTree.shallow
  preserves := fun related selected clauses => related.shallow selected clauses

end EffectSemantics
