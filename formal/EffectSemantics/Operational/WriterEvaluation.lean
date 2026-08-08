import EffectSemantics.Denotational.WriterTree

namespace EffectSemantics

/-- Operational production of a finite Writer/free behavior tree. Operation
zero is the concrete Writer `tell`; its response is unit. -/
inductive ProducesWriterTree : Comp → WriterTree Val → Prop where
  | returned : ProducesWriterTree (.ret value) (.ret value)
  | internal : Step term next → ProducesWriterTree next tree →
      ProducesWriterTree term tree
  | tell : ExposesBase term request → request.operation = 0 →
      ProducesWriterTree (request.resume .unit) tail →
      ProducesWriterTree term (.tell request.parameter tail)
  | free : ExposesFree term request →
      (∀ response, ProducesWriterTree (request.resume response)
        (continuation response)) →
      ProducesWriterTree term
        (.free request.interface request.operation request.parameter continuation)

/-- Direct terminating Writer observation on source computations. -/
inductive WriterRuns : Comp → List Val → Val → Prop where
  | returned : WriterRuns (.ret value) [] value
  | internal : Step term next → WriterRuns next log value →
      WriterRuns term log value
  | tell : ExposesBase term request → request.operation = 0 →
      WriterRuns (request.resume .unit) log value →
      WriterRuns term (request.parameter :: log) value

/-- Tree observation implies the corresponding source-level Writer run. -/
theorem ProducesWriterTree.sound
    (produces : ProducesWriterTree term tree)
    (observes : WriterTree.Observes tree log value) :
    WriterRuns term log value := by
  induction produces generalizing log value with
  | returned =>
      cases observes
      exact .returned
  | internal step produces ih =>
      exact .internal step (ih observes)
  | tell exposed selected produces ih =>
      cases observes with
      | tell tailObservation =>
          exact .tell exposed selected (ih tailObservation)
  | free exposed produces ih => cases observes

/-- Every direct Writer run has a finite behavior tree with the same ground
observation.  Together with `sound`, this is the concrete operational/tree
adequacy equivalence for terminating Writer runs. -/
theorem WriterRuns.complete (runs : WriterRuns term log value) :
    ∃ tree, ProducesWriterTree term tree ∧
      WriterTree.Observes tree log value := by
  induction runs with
  | returned => exact ⟨.ret _, .returned, .ret⟩
  | internal step runs ih =>
      obtain ⟨tree, produces, observes⟩ := ih
      exact ⟨tree, .internal step produces, observes⟩
  | tell exposed selected runs ih =>
      obtain ⟨tree, produces, observes⟩ := ih
      exact ⟨.tell _ tree, .tell exposed selected produces, .tell observes⟩

theorem writer_operational_tree_adequacy :
    WriterRuns term log value ↔
      ∃ tree, ProducesWriterTree term tree ∧
        WriterTree.Observes tree log value :=
  ⟨WriterRuns.complete, fun ⟨_, produces, observes⟩ =>
    produces.sound observes⟩

end EffectSemantics
