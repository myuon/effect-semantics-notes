import EffectSemantics.Theory.GenericFreeExtension

namespace EffectSemantics

open GenericExtensionAlgebra

/-!
# Concrete signatures for the generic free extension

Writer is related explicitly to the pre-existing concrete `WriterTree`.
State and Exception exhibit the typed one-layer signatures needed by the same
generic construction.
-/

inductive WriterBaseOp where
  | tell (message : Val)

abbrev writerBaseSignature : OperationSignature where
  Op := WriterBaseOp
  Response := fun _ => Unit

structure UserOperation where
  interface : Nat
  operation : Nat
  parameter : Val

def userOperationSignature : OperationSignature where
  Op := UserOperation
  Response := fun _ => Val

def writerToGeneric : WriterTree α →
    FreeExtension writerBaseSignature userOperationSignature α
  | .ret value => .ret value
  | .tell message next =>
      .baseOp (.tell message) (fun _ => writerToGeneric next)
  | .free interface operation parameter continuation =>
      .freeOp ⟨interface, operation, parameter⟩
        (fun response => writerToGeneric (continuation response))

def genericToWriter :
    FreeExtension writerBaseSignature userOperationSignature α → WriterTree α
  | .ret value => .ret value
  | .baseOp (.tell message) continuation =>
      .tell message (genericToWriter (continuation ()))
  | .freeOp request continuation =>
      .free request.interface request.operation request.parameter
        (fun response => genericToWriter (continuation response))

theorem genericToWriter_writerToGeneric (tree : WriterTree α) :
    genericToWriter (writerToGeneric tree) = tree := by
  induction tree with
  | ret => rfl
  | tell message next ih => simp [writerToGeneric, genericToWriter, ih]
  | free interface operation parameter continuation ih =>
      simp only [writerToGeneric, genericToWriter]
      congr
      funext response
      exact ih response

theorem writerToGeneric_genericToWriter
    (tree : FreeExtension writerBaseSignature userOperationSignature α) :
    writerToGeneric (genericToWriter tree) = tree := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih =>
      cases operation with
      | tell message =>
          simp only [genericToWriter, writerToGeneric]
          congr
          funext response
          cases response
          exact ih ()
  | freeOp request continuation ih =>
      rcases request with ⟨interface, operation, parameter⟩
      simp only [genericToWriter, writerToGeneric]
      congr
      funext response
      exact ih response

theorem writerToGeneric_bind (tree : WriterTree α)
    (next : α → WriterTree β) :
    writerToGeneric (tree.bind next) =
      (writerToGeneric tree).bind (fun value => writerToGeneric (next value)) := by
  induction tree with
  | ret => rfl
  | tell message tail ih => simp [WriterTree.bind, writerToGeneric, ih]
  | free interface operation parameter continuation ih =>
      simp only [WriterTree.bind, writerToGeneric, FreeExtension.bind]
      congr
      funext response
      exact ih response

inductive StateBaseOp where
  | get
  | put (state : Bool)

abbrev stateBaseSignature : OperationSignature where
  Op := StateBaseOp
  Response
    | .get => Bool
    | .put _ => Unit

inductive ExceptionBaseOp where
  | raise (error : Val)

abbrev exceptionBaseSignature : OperationSignature where
  Op := ExceptionBaseOp
  Response
    | .raise _ => Empty

/-! ## Dedicated operational Writer monad and model comparison -/

abbrev WriterOutcome (α : Type) := Option (List Val × α)

def WriterOutcome.pure (value : α) : WriterOutcome α := some ([], value)

def WriterOutcome.bind (result : WriterOutcome α)
    (next : α → WriterOutcome β) : WriterOutcome β :=
  match result with
  | none => none
  | some (firstLog, value) =>
      match next value with
      | none => none
      | some (secondLog, resultValue) =>
          some (firstLog ++ secondLog, resultValue)

theorem WriterOutcome.bind_pure (result : WriterOutcome α) :
    WriterOutcome.bind result WriterOutcome.pure = result := by
  cases result with
  | none => rfl
  | some result => rcases result with ⟨log, value⟩; simp [WriterOutcome.bind, WriterOutcome.pure]

theorem WriterOutcome.bind_assoc (result : WriterOutcome α)
    (first : α → WriterOutcome β) (second : β → WriterOutcome γ) :
    WriterOutcome.bind (WriterOutcome.bind result first) second =
      WriterOutcome.bind result (fun value => WriterOutcome.bind (first value) second) := by
  cases result with
  | none => rfl
  | some result =>
      rcases result with ⟨firstLog, value⟩
      cases foundFirst : first value with
      | none => simp [WriterOutcome.bind, foundFirst]
      | some result =>
          rcases result with ⟨secondLog, middleValue⟩
          cases foundSecond : second middleValue with
          | none => simp [WriterOutcome.bind, foundFirst, foundSecond]
          | some result =>
              rcases result with ⟨thirdLog, resultValue⟩
              simp [WriterOutcome.bind, foundFirst, foundSecond, List.append_assoc]

def writerOutcomeMonad : MonadStructure WriterOutcome where
  pure := WriterOutcome.pure
  bind := WriterOutcome.bind
  leftUnit := by
    intro α β value next
    cases found : next value <;> simp [WriterOutcome.bind, WriterOutcome.pure, found]
  rightUnit := WriterOutcome.bind_pure
  associative := WriterOutcome.bind_assoc

def WriterOutcome.tell (message : Val) (next : WriterOutcome α) : WriterOutcome α :=
  match next with
  | none => none
  | some (log, value) => some (message :: log, value)

theorem WriterOutcome.tell_bind (message : Val) (result : WriterOutcome α)
    (next : α → WriterOutcome β) :
    WriterOutcome.bind (WriterOutcome.tell message result) next =
      WriterOutcome.tell message (WriterOutcome.bind result next) := by
  cases result with
  | none => rfl
  | some result =>
      rcases result with ⟨log, value⟩
      cases found : next value <;> simp [WriterOutcome.tell, WriterOutcome.bind, found]

def writerOutcomeAlgebra :
    GenericExtensionAlgebra writerBaseSignature userOperationSignature WriterOutcome where
  monad := writerOutcomeMonad
  interpretBase
    | .tell message, continuation => WriterOutcome.tell message (continuation ())
  interpretFree := fun _ _ => none
  baseBind := by
    intro α β operation continuation next
    cases operation with
    | tell message =>
        change WriterOutcome.bind (WriterOutcome.tell message (continuation ())) next =
          WriterOutcome.tell message (WriterOutcome.bind (continuation ()) next)
        exact WriterOutcome.tell_bind message (continuation ()) next
  freeBind := by
    intro α β operation continuation next
    change WriterOutcome.bind none next = none
    rfl

/-- Compositional interpretation in the dedicated operational Writer monad.
This is the Lean counterpart of `⟦-⟧_S`, not direct small-step execution. -/
def genericWriterOperationalInterpretation
    (tree : FreeExtension writerBaseSignature userOperationSignature α) :
    WriterOutcome α := writerOutcomeAlgebra.fold tree

theorem genericInitialAlgebra_fold (tree : FreeExtension base free α) :
    (genericInitialAlgebra base free).fold tree = tree := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih =>
      simp only [GenericExtensionAlgebra.fold, genericInitialAlgebra]
      congr
      funext response
      exact ih response
  | freeOp operation continuation ih =>
      simp only [GenericExtensionAlgebra.fold, genericInitialAlgebra]
      congr
      funext response
      exact ih response

def genericWriterObservationMorphism :
    GenericExtensionAlgebra.Morphism
      (genericInitialAlgebra writerBaseSignature userOperationSignature)
      writerOutcomeAlgebra where
  map := genericWriterOperationalInterpretation
  pure := fun _ => rfl
  bind := fun tree next =>
    GenericExtensionAlgebra.fold_bind writerOutcomeAlgebra tree next
  preservesBase := fun _ _ => rfl
  preservesFree := fun _ _ => rfl

/-- The canonical finite comparison from the structural/denotational tree
model to the dedicated operational Writer monad.  In particular, the Writer
effect is carried by `WriterOutcome`; it is not packed into an observation and
then wrapped in `Id`. -/
def genericWriterModelComparison :
    GenericExtensionAlgebra.ModelComparison
      (genericInitialAlgebra writerBaseSignature userOperationSignature)
      writerOutcomeAlgebra where
  comparison := genericWriterObservationMorphism

theorem genericWriter_finite_model_comparison
    (tree : FreeExtension writerBaseSignature userOperationSignature α) :
    genericWriterOperationalInterpretation tree = writerOutcomeAlgebra.fold tree := by
  have compared := genericWriterModelComparison.lift tree
  rw [genericInitialAlgebra_fold] at compared
  exact compared

theorem genericWriter_finite_adequacy
    (tree : FreeExtension writerBaseSignature userOperationSignature α) :
    genericWriterOperationalInterpretation tree = writerOutcomeAlgebra.fold tree := by
  exact genericWriter_finite_model_comparison tree

/-- The generic Writer observation is extensionally the existing concrete
`WriterTree.runClosed`; this prevents the abstract adequacy theorem from being
a disconnected duplicate model. -/
theorem genericWriterOperationalInterpretation_writerToGeneric (tree : WriterTree α) :
    genericWriterOperationalInterpretation (writerToGeneric tree) =
      WriterTree.runClosed tree := by
  induction tree with
  | ret value =>
      change WriterOutcome.pure value = some ([], value)
      rfl
  | tell message next ih =>
      change WriterOutcome.tell message
          (genericWriterOperationalInterpretation (writerToGeneric next)) =
        (WriterTree.runClosed next).map
          (fun result => (message :: result.1, result.2))
      rw [ih]
      cases WriterTree.runClosed next <;> rfl
  | free interface operation parameter continuation ih =>
      change none = none
      rfl

/-! ## Dedicated operational State monad and model comparison -/

abbrev StateOutcome (α : Type) := Bool → Option (α × Bool)

def StateOutcome.pure (value : α) : StateOutcome α :=
  fun state => some (value, state)

def StateOutcome.bind (result : StateOutcome α)
    (next : α → StateOutcome β) : StateOutcome β :=
  fun state =>
    match result state with
    | none => none
    | some (value, nextState) => next value nextState

def stateOutcomeMonad : MonadStructure StateOutcome where
  pure := StateOutcome.pure
  bind := StateOutcome.bind
  leftUnit := by intro α β value next; rfl
  rightUnit := by
    intro α result
    funext state
    cases found : result state <;>
      simp [StateOutcome.bind, StateOutcome.pure, found]
  associative := by
    intro α β γ result first second
    funext state
    cases found : result state with
    | none => simp [StateOutcome.bind, found]
    | some result =>
        rcases result with ⟨value, nextState⟩
        cases nextFound : first value nextState <;>
          simp [StateOutcome.bind, found, nextFound]

def stateOutcomeAlgebra :
    GenericExtensionAlgebra stateBaseSignature userOperationSignature
      StateOutcome where
  monad := stateOutcomeMonad
  interpretBase
    | .get, continuation => fun state => continuation state state
    | .put nextState, continuation => fun _ => continuation () nextState
  interpretFree := fun _ _ _ => none
  baseBind := by intro α β operation continuation next; cases operation <;> rfl
  freeBind := by intro α β operation continuation next; rfl

/-- Compositional interpretation `⟦-⟧_S` in the operational State monad. -/
def genericStateOperationalInterpretation
    (tree : FreeExtension stateBaseSignature userOperationSignature α) :
    StateOutcome α := stateOutcomeAlgebra.fold tree

def genericToState :
    FreeExtension stateBaseSignature userOperationSignature α → StateTree α
  | .ret value => .ret value
  | .baseOp .get continuation => .get (fun state =>
      genericToState (continuation state))
  | .baseOp (.put state) continuation => .put state
      (genericToState (continuation ()))
  | .freeOp request continuation =>
      .free request.interface request.operation request.parameter
        (fun response => genericToState (continuation response))

/-- Machine soundness for the concrete finite State evaluator. -/
theorem genericStateOperationalInterpretation_runClosed
    (tree : FreeExtension stateBaseSignature userOperationSignature α) :
    genericStateOperationalInterpretation tree =
      StateTree.runClosed (genericToState tree) := by
  funext state
  induction tree generalizing state with
  | ret => rfl
  | baseOp operation continuation ih =>
      cases operation with
      | get => exact ih state state
      | put nextState => exact ih () nextState
  | freeOp => rfl

def genericStateModelComparison :
    GenericExtensionAlgebra.ModelComparison
      (genericInitialAlgebra stateBaseSignature userOperationSignature)
      stateOutcomeAlgebra :=
  GenericExtensionAlgebra.initialModelComparison stateOutcomeAlgebra

/-! ## Dedicated operational Exception monad and model comparison -/

abbrev ExceptionOutcome (α : Type) := Except Val α

def ExceptionOutcome.pure (value : α) : ExceptionOutcome α := .ok value

def ExceptionOutcome.bind (result : ExceptionOutcome α)
    (next : α → ExceptionOutcome β) : ExceptionOutcome β :=
  match result with
  | .error error => .error error
  | .ok value => next value

def exceptionOutcomeMonad : MonadStructure ExceptionOutcome where
  pure := ExceptionOutcome.pure
  bind := ExceptionOutcome.bind
  leftUnit := by intro α β value next; rfl
  rightUnit := by intro α result; cases result <;> rfl
  associative := by
    intro α β γ result first second
    cases result with
    | error => rfl
    | ok value => cases first value <;> rfl

def exceptionOutcomeAlgebra :
    GenericExtensionAlgebra exceptionBaseSignature userOperationSignature
      ExceptionOutcome where
  monad := exceptionOutcomeMonad
  interpretBase
    | .raise error, _ => .error error
  interpretFree := fun _ _ => .error .unit
  baseBind := by intro α β operation continuation next; cases operation <;> rfl
  freeBind := by intro α β operation continuation next; rfl

/-- Compositional interpretation `⟦-⟧_S` in the operational Exception monad. -/
def genericExceptionOperationalInterpretation
    (tree : FreeExtension exceptionBaseSignature userOperationSignature α) :
    ExceptionOutcome α := exceptionOutcomeAlgebra.fold tree

def genericToException :
    FreeExtension exceptionBaseSignature userOperationSignature α →
      ExceptionTree α
  | .ret value => .ret value
  | .baseOp (.raise error) _ => .raise error
  | .freeOp request continuation =>
      .free request.interface request.operation request.parameter
        (fun response => genericToException (continuation response))

/-- Machine soundness for the concrete finite Exception evaluator. -/
theorem genericExceptionOperationalInterpretation_runClosed
    (tree : FreeExtension exceptionBaseSignature userOperationSignature α) :
    genericExceptionOperationalInterpretation tree =
      ExceptionTree.runClosed (genericToException tree) := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih => cases operation <;> rfl
  | freeOp => rfl

def genericExceptionModelComparison :
    GenericExtensionAlgebra.ModelComparison
      (genericInitialAlgebra exceptionBaseSignature userOperationSignature)
      exceptionOutcomeAlgebra :=
  GenericExtensionAlgebra.initialModelComparison exceptionOutcomeAlgebra

end EffectSemantics
