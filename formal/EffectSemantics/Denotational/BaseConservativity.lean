import EffectSemantics.Operational.WriterEvaluation
import EffectSemantics.Metatheory.BaseConservativity

namespace EffectSemantics
namespace WriterTree

def BaseOnly : WriterTree α → Prop
  | .ret _ => True
  | .tell _ tail => tail.BaseOnly
  | .free _ _ _ _ => False

end WriterTree

/-- Denotational old-language conservativity: every finite Writer behavior
tree produced by a syntactically old computation contains no free node. -/
theorem ProducesWriterTree.baseOnly
    (produces : ProducesWriterTree term tree) (termOnly : term.BaseOnly) :
    tree.BaseOnly := by
  induction produces with
  | returned => trivial
  | internal step produces ih =>
      exact ih (step.preservesBaseOnly termOnly)
  | tell exposed selected produces ih =>
      rw [exposed] at termOnly
      have resumedOnly := BaseRequest.resume_baseOnly termOnly
        (show Val.unit.BaseOnly from trivial)
      exact ih resumedOnly
  | free exposed produces ih =>
      rename_i sourceTerm request continuation
      have head : sourceTerm.head = .free request := by
        rw [exposed]
        exact FreeRequest.source_head request
      exact False.elim (Comp.baseOnly_head_not_free termOnly request head)

theorem baseOnly_writer_tree_has_no_free
    (termOnly : term.BaseOnly) (produces : ProducesWriterTree term tree) :
    tree.BaseOnly := produces.baseOnly termOnly

theorem WriterTree.shallow_baseOnly (treeOnly : tree.BaseOnly)
    (selected : Nat) (handler : WriterTree.AffineSemantics) :
    WriterTree.shallow selected handler tree = tree := by
  induction tree with
  | ret value => rfl
  | tell message tail ih => simp [WriterTree.shallow, ih treeOnly]
  | free => contradiction

/-- Adding and running a shallow handler is denotationally conservative on
old-language Writer behaviors. -/
theorem ProducesWriterTree.shallow_conservative
    (produces : ProducesWriterTree term tree) (termOnly : term.BaseOnly)
    (selected : Nat) (handler : WriterTree.AffineSemantics) :
    WriterTree.shallow selected handler tree = tree :=
  WriterTree.shallow_baseOnly (produces.baseOnly termOnly) selected handler

end EffectSemantics
