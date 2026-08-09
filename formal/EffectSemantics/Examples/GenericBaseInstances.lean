import EffectSemantics.Certificate.GenericFreeExtension

namespace EffectSemantics

/-!
# Concrete signatures for the generic free extension

Writer is related explicitly to the pre-existing concrete `WriterTree`.
State and Exception exhibit the typed one-layer signatures needed by the same
generic construction.
-/

inductive WriterBaseOp where
  | tell (message : Val)

def writerBaseSignature : OperationSignature where
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

def stateBaseSignature : OperationSignature where
  Op := StateBaseOp
  Response
    | .get => Bool
    | .put _ => Unit

inductive ExceptionBaseOp where
  | raise (error : Val)

def exceptionBaseSignature : OperationSignature where
  Op := ExceptionBaseOp
  Response
    | .raise _ => Empty

def genericWriterExtensionCert :
    GenericFreeExtensionCert writerBaseSignature userOperationSignature :=
  genericFreeExtensionStructurePreservation _ _

def genericStateExtensionCert :
    GenericFreeExtensionCert stateBaseSignature userOperationSignature :=
  genericFreeExtensionStructurePreservation _ _

def genericExceptionExtensionCert :
    GenericFreeExtensionCert exceptionBaseSignature userOperationSignature :=
  genericFreeExtensionStructurePreservation _ _

end EffectSemantics
