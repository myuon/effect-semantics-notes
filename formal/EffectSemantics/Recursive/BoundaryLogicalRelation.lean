import EffectSemantics.Recursive.DeepWriterBoundary

namespace EffectSemantics

def RecursiveValueRelation (sig : Signature) (ty : Ty) (value : Val) : Prop :=
  Nonempty (HasVal sig [] value ty)

/-- Type-indexed interpretation of every outward observation.  A request is
well typed when its reconstructed source computation still has the original
result type; its intermediate effect bound is existential. -/
inductive TypedDeepWriterBoundary (sig : Signature) (resultTy : Ty) :
    DeepWriterBoundary → Prop where
  | returned : RecursiveValueRelation sig resultTy value →
      TypedDeepWriterBoundary sig resultTy (.returned log value)
  | base : Nonempty (HasComp sig [] request.source resultTy effect) →
      TypedDeepWriterBoundary sig resultTy (.base log request)
  | free : Nonempty (HasComp sig [] request.source resultTy effect) →
      TypedDeepWriterBoundary sig resultTy (.free log request)

theorem TypedDeepWriterBoundary.prepend
    (typed : TypedDeepWriterBoundary sig resultTy boundary) :
    TypedDeepWriterBoundary sig resultTy (boundary.prepend entry) := by
  cases typed with
  | returned valueTyping => exact .returned valueTyping
  | base requestTyping => exact .base requestTyping
  | free requestTyping => exact .free requestTyping

/-- Fundamental boundary-safety lemma for the recursive Writer/deep-handler
instance.  It covers recursive-function unfolding through ordinary
preservation and all return/base/free boundary forms. -/
theorem observeDeepWriterBoundary_typed
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (writerUnit : WriterResponseUnit sig)
    (observed : term.observeDeepWriterBoundary fuel interface handler =
      some boundary) :
    TypedDeepWriterBoundary sig resultTy boundary := by
  induction fuel generalizing term effect boundary with
  | zero => simp [Comp.observeDeepWriterBoundary] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value =>
          simp [Comp.observeDeepWriterBoundary, found] at observed
          subst boundary
          have source := Comp.head_returned_sound found
          subst term
          exact .returned ⟨typing.returnView.valueTyping⟩
      | internal next =>
          simp only [Comp.observeDeepWriterBoundary, found] at observed
          obtain ⟨step⟩ := Comp.head_internal_sound found
          exact ih (step.preserve typing) observed
      | base request =>
          have exposed := Comp.head_base_sound found
          rw [exposed] at typing
          let requestTyping := typing.exposedBaseView
          by_cases selected : request.operation = 0
          · simp only [Comp.observeDeepWriterBoundary, found, selected, if_pos,
              Option.map_eq_some_iff] at observed
            obtain ⟨tail, tailObserved, transformed⟩ := observed
            have responseEq : requestTyping.responseTy = .unit := by
              apply writerUnit requestTyping.parameterTy requestTyping.responseTy
              simpa [selected] using requestTyping.lookup
            have unitTyping : HasVal sig [] .unit requestTyping.responseTy := by
              rw [responseEq]
              exact .unit
            have tailTyped := ih (requestTyping.resumeTyping unitTyping) tailObserved
            rw [← transformed]
            exact tailTyped.prepend
          · simp [Comp.observeDeepWriterBoundary, found, selected] at observed
            subst boundary
            exact .base ⟨typing⟩
      | free request =>
          have exposed := Comp.head_free_sound found
          rw [exposed] at typing
          by_cases same : request.interface = interface
          · cases clauseFound : handler.lookup request.operation with
            | some clause =>
                simp only [Comp.observeDeepWriterBoundary, found, same, if_pos,
                  clauseFound] at observed
                exact ih (handlerTyping.answerWithTyping typing same clauseFound)
                  observed
            | none =>
                simp [Comp.observeDeepWriterBoundary, found, same, clauseFound]
                  at observed
                subst boundary
                exact .free ⟨typing⟩
          · simp [Comp.observeDeepWriterBoundary, found, same] at observed
            subst boundary
            exact .free ⟨typing⟩
      | stuck => simp [Comp.observeDeepWriterBoundary, found] at observed

def RecursiveComputationRelation (sig : Signature) (resultTy : Ty)
    (interface : Nat) (handler : AffineHandler) (term : Comp) : Prop :=
  ∀ boundary, term.deepWriterBoundaryLimit interface handler = some boundary →
    TypedDeepWriterBoundary sig resultTy boundary

def RecursiveEnvironmentRelation (sig : Signature) (ctx : Context)
    (substitution : Nat → Val) : Prop :=
  Nonempty (SubstPreserves sig ctx [] substitution)

/-- Type-indexed fundamental theorem for closed computations in the concrete
recursive Writer model. -/
theorem recursive_writer_fundamental
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (writerUnit : WriterResponseUnit sig) :
    RecursiveComputationRelation sig resultTy interface handler term := by
  intro boundary observed
  obtain ⟨fuel, finite⟩ := Comp.deepWriterBoundaryLimit_some_witness observed
  exact observeDeepWriterBoundary_typed typing handlerTyping writerUnit finite

theorem recursive_writer_finite_pole
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (writerUnit : WriterResponseUnit sig) :
    StableObservation.Satisfies (TypedDeepWriterBoundary sig resultTy)
      (term.deepWriterBoundaryApprox interface handler) := by
  intro fuel boundary observed
  exact observeDeepWriterBoundary_typed typing handlerTyping writerUnit observed

theorem recursive_writer_typed_pole_admissible :
    StableObservation.Admissible
      (StableObservation.Satisfies
        (TypedDeepWriterBoundary sig resultTy)) :=
  StableObservation.satisfies_admissible _

theorem recursive_value_fundamental_open
    (typing : HasVal sig ctx value ty)
    (environment : RecursiveEnvironmentRelation sig ctx substitution) :
    RecursiveValueRelation sig ty (value.subst substitution) := by
  obtain ⟨preserves⟩ := environment
  exact ⟨typing.subst_preserved preserves⟩

/-- Open-term fundamental theorem.  Every logically related closing
substitution turns a typed computation—including recursive functions—into a
closed computation related to all of its finite outward observations. -/
theorem recursive_writer_fundamental_open
    (typing : HasComp sig ctx term resultTy effect)
    (environment : RecursiveEnvironmentRelation sig ctx substitution)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (writerUnit : WriterResponseUnit sig) :
    RecursiveComputationRelation sig resultTy interface handler
      (term.subst substitution) := by
  obtain ⟨preserves⟩ := environment
  exact recursive_writer_fundamental (typing.subst_preserved preserves)
    handlerTyping writerUnit

/-- The same fundamental relation simultaneously gives selected-interface
discharge when the typed handler is exhaustive. -/
theorem recursive_writer_fundamental_discharges
    (typing : HasComp sig [] term resultTy effect)
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (exhaustive : handler.Exhaustive sig interface)
    (writerUnit : WriterResponseUnit sig)
    (observed : term.deepWriterBoundaryLimit interface handler =
      some (.free log request)) :
    TypedDeepWriterBoundary sig resultTy (.free log request) ∧
      request.interface ≠ interface :=
  ⟨recursive_writer_fundamental typing handlerTyping writerUnit _ observed,
    deepWriterBoundaryLimit_discharges typing handlerTyping exhaustive
      writerUnit observed⟩

end EffectSemantics
