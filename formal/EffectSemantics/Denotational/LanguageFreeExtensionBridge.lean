import EffectSemantics.Denotational.LanguageWriterTree
import EffectSemantics.Denotational.GenericFreeExtension

namespace EffectSemantics

/-- The Writer operation carried by `LanguageWriterTree`; its parameter is the
message itself and its response is unit. -/
def languageWriterBaseSignature : OperationSignature where
  Op := FinLanguageVal
  Response := fun _ => Unit

/-- A well-typed free-operation request, including the source parameter. -/
structure LanguageFreeOperation (sig : LanguageSignature) where
  interface : Nat
  operation : Nat
  parameterTy : LanguageTy
  responseTy : LanguageTy
  lookup : sig.free interface operation = some ⟨parameterTy, responseTy⟩
  parameter : LanguageClosedVal sig parameterTy

def languageFreeSignature (sig : LanguageSignature) : OperationSignature where
  Op := LanguageFreeOperation sig
  Response := fun operation => LanguageClosedVal sig operation.responseTy

/-- Forget the language-specific presentation of a response tree while
retaining all typed requests in the generic finite free extension. -/
def LanguageWriterTree.toFreeExtension (tree : LanguageWriterTree sig α) :
    FreeExtension languageWriterBaseSignature (languageFreeSignature sig) α :=
  match tree with
  | .ret value => .ret value
  | .tell message tail =>
      .baseOp message (fun _ => tail.toFreeExtension)
  | .free interface operation lookup parameter continuation =>
      .freeOp ⟨interface, operation, _, _, lookup, parameter⟩
        (fun response => (continuation response).toFreeExtension)

/-- The source-tree bridge preserves semantic sequencing exactly. -/
theorem LanguageWriterTree.toFreeExtension_bind
    (tree : LanguageWriterTree sig α)
    (next : α → LanguageWriterTree sig β) :
    (tree.bind next).toFreeExtension =
      tree.toFreeExtension.bind (fun value => (next value).toFreeExtension) := by
  induction tree with
  | ret => rfl
  | tell message tail ih =>
      simp only [LanguageWriterTree.bind, LanguageWriterTree.toFreeExtension,
        FreeExtension.bind]
      congr
      funext response
      exact ih
  | free interface operation lookup parameter continuation ih =>
      simp only [LanguageWriterTree.bind, LanguageWriterTree.toFreeExtension,
        FreeExtension.bind]
      congr
      funext response
      exact ih response

end EffectSemantics
