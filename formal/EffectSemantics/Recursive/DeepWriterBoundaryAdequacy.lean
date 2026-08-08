import EffectSemantics.Recursive.BoundaryLogicalRelation

namespace EffectSemantics

/-- Direct operational boundary semantics for the recursively reinstalled
Writer handler. -/
inductive DeepWriterBoundaryRuns (interface : Nat) (handler : AffineHandler) :
    Comp → DeepWriterBoundary → Prop where
  | returned : DeepWriterBoundaryRuns interface handler (.ret value)
      (.returned [] value)
  | internal : Step term next →
      DeepWriterBoundaryRuns interface handler next boundary →
      DeepWriterBoundaryRuns interface handler term boundary
  | tell : ExposesBase term request → request.operation = 0 →
      DeepWriterBoundaryRuns interface handler (request.resume .unit) boundary →
      DeepWriterBoundaryRuns interface handler term
        (boundary.prepend request.parameter)
  | baseOut : ExposesBase term request → request.operation ≠ 0 →
      DeepWriterBoundaryRuns interface handler term (.base [] request)
  | matched : ExposesFree term request → request.interface = interface →
      handler.lookup request.operation = some clause →
      DeepWriterBoundaryRuns interface handler (request.answerWith clause) boundary →
      DeepWriterBoundaryRuns interface handler term boundary
  | freeOther : ExposesFree term request → request.interface ≠ interface →
      DeepWriterBoundaryRuns interface handler term (.free [] request)
  | freeMissing : ExposesFree term request → request.interface = interface →
      handler.lookup request.operation = none →
      DeepWriterBoundaryRuns interface handler term (.free [] request)

theorem DeepWriterBoundaryRuns.to_observation
    (runs : DeepWriterBoundaryRuns interface handler term boundary) :
    ∃ fuel, term.observeDeepWriterBoundary fuel interface handler =
      some boundary := by
  induction runs with
  | returned => exact ⟨1, rfl⟩
  | internal step runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      exact ⟨fuel + 1, by
        simp [Comp.observeDeepWriterBoundary, step.to_head, observed]⟩
  | tell exposed selected runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [exposed]
      simp [Comp.observeDeepWriterBoundary, BaseRequest.source_head,
        selected, observed]
  | baseOut exposed notSelected =>
      exact ⟨1, by
        rw [exposed]
        simp [Comp.observeDeepWriterBoundary, BaseRequest.source_head,
          notSelected]⟩
  | matched exposed same found runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [exposed]
      simp [Comp.observeDeepWriterBoundary, FreeRequest.source_head,
        same, found, observed]
  | freeOther exposed different =>
      exact ⟨1, by
        rw [exposed]
        simp [Comp.observeDeepWriterBoundary, FreeRequest.source_head,
          different]⟩
  | freeMissing exposed same missing =>
      exact ⟨1, by
        rw [exposed]
        simp [Comp.observeDeepWriterBoundary, FreeRequest.source_head,
          same, missing]⟩

theorem Comp.observeDeepWriterBoundary_reflects
    (observed : term.observeDeepWriterBoundary fuel interface handler =
      some boundary) :
    DeepWriterBoundaryRuns interface handler term boundary := by
  induction fuel generalizing term boundary with
  | zero => simp [Comp.observeDeepWriterBoundary] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value =>
          simp [Comp.observeDeepWriterBoundary, found] at observed
          subst boundary
          have source := Comp.head_returned_sound found
          subst term
          exact .returned
      | internal next =>
          simp only [Comp.observeDeepWriterBoundary, found] at observed
          obtain ⟨step⟩ := Comp.head_internal_sound found
          exact .internal step (ih observed)
      | base request =>
          by_cases selected : request.operation = 0
          · simp only [Comp.observeDeepWriterBoundary, found, selected, if_pos,
              Option.map_eq_some_iff] at observed
            obtain ⟨tail, tailObserved, transformed⟩ := observed
            rw [← transformed]
            exact .tell (Comp.head_base_sound found) selected (ih tailObserved)
          · simp [Comp.observeDeepWriterBoundary, found, selected] at observed
            subst boundary
            exact .baseOut (Comp.head_base_sound found) selected
      | free request =>
          by_cases same : request.interface = interface
          · cases clauseFound : handler.lookup request.operation with
            | some clause =>
                simp only [Comp.observeDeepWriterBoundary, found, same, if_pos,
                  clauseFound] at observed
                exact .matched (Comp.head_free_sound found) same clauseFound
                  (ih observed)
            | none =>
                simp [Comp.observeDeepWriterBoundary, found, same, clauseFound]
                  at observed
                subst boundary
                exact .freeMissing (Comp.head_free_sound found) same clauseFound
          · simp [Comp.observeDeepWriterBoundary, found, same] at observed
            subst boundary
            exact .freeOther (Comp.head_free_sound found) same
      | stuck => simp [Comp.observeDeepWriterBoundary, found] at observed

theorem deep_writer_boundary_finite_adequacy :
    DeepWriterBoundaryRuns interface handler term boundary ↔
      ∃ fuel, term.observeDeepWriterBoundary fuel interface handler =
        some boundary := by
  constructor
  · exact DeepWriterBoundaryRuns.to_observation
  · rintro ⟨fuel, observed⟩
    exact Comp.observeDeepWriterBoundary_reflects observed

theorem deep_writer_boundary_limit_adequacy :
    DeepWriterBoundaryRuns interface handler term boundary ↔
      term.deepWriterBoundaryLimit interface handler = some boundary := by
  rw [deep_writer_boundary_finite_adequacy]
  constructor
  · rintro ⟨fuel, observed⟩
    exact Comp.deepWriterBoundaryLimit_of_observed observed
  · exact Comp.deepWriterBoundaryLimit_some_witness

end EffectSemantics
