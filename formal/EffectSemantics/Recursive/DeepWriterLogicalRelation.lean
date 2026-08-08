import EffectSemantics.Recursive.DeepWriterContinuity

namespace EffectSemantics

namespace DeepWriterPredicate

def Admissible (predicate : DeepWriterApproximation → Prop) : Prop :=
  ∀ chain : DeepWriterChain,
    (∀ index, predicate (chain.sequence index)) → predicate chain.sup

def ContainsBottom (predicate : DeepWriterApproximation → Prop) : Prop :=
  predicate (fun _ => none)

def ClosedBy (predicate : DeepWriterApproximation → Prop)
    (interface : Nat) (handler : AffineHandler) : Prop :=
  ∀ approximation, predicate approximation →
    predicate (deepWriterFunctional interface handler approximation)

/-- Admissible fixed-point induction specialized to the recursively
reinstalled Writer handler. -/
theorem deepWriterLimit_induction
    (admissible : Admissible predicate)
    (bottom : ContainsBottom predicate)
    (closed : ClosedBy predicate interface handler) :
    predicate (deepWriterLimitFamily interface handler) := by
  rw [← deepWriterKleeneSup_eq_limit interface handler]
  apply admissible (deepWriterKleeneChain interface handler)
  intro index
  induction index with
  | zero =>
      change predicate (fun _ => none)
      exact bottom
  | succ index ih =>
      simpa [deepWriterKleeneChain, iterateDeepWriter] using closed _ ih

end DeepWriterPredicate

/-- A pole-style lifting: every finite result exposed by an approximation
must satisfy the chosen source/result observation relation. -/
def DeepWriterSatisfies
    (pole : Comp → List Val → Val → Prop)
    (approximation : DeepWriterApproximation) : Prop :=
  ∀ term log value, approximation term = some (log, value) →
    pole term log value

theorem DeepWriterSatisfies.bottom (pole : Comp → List Val → Val → Prop) :
    DeepWriterSatisfies pole (fun _ => none) := by
  intro _ _ _ observed
  cases observed

theorem DeepWriterSatisfies.admissible
    (pole : Comp → List Val → Val → Prop) :
    DeepWriterPredicate.Admissible (DeepWriterSatisfies pole) := by
  intro chain all term log value observed
  obtain ⟨index, finite⟩ := chain.sup_some_witness observed
  exact all index term log value finite

/-- Fixed-point induction for an arbitrary finite-observation pole.  The only
semantic obligation left to a logical-relation proof is closure under one
handler layer. -/
theorem deepWriterLimit_satisfies
    (oneLayer : ∀ approximation,
      DeepWriterSatisfies pole approximation →
      DeepWriterSatisfies pole
        (deepWriterFunctional interface handler approximation)) :
    DeepWriterSatisfies pole (deepWriterLimitFamily interface handler) :=
  DeepWriterPredicate.deepWriterLimit_induction
    (DeepWriterSatisfies.admissible pole)
    (DeepWriterSatisfies.bottom pole)
    oneLayer

/-- The operational run pole is one-layer closed, so fixed-point induction
recovers the limit adequacy direction without induction on fuel. -/
theorem deepWriterRuns_oneLayer
    (approximation : DeepWriterApproximation)
    (sound : DeepWriterSatisfies
      (fun term log value => DeepWriterRuns interface handler term log value)
      approximation) :
    DeepWriterSatisfies
      (fun term log value => DeepWriterRuns interface handler term log value)
      (deepWriterFunctional interface handler approximation) := by
  intro term log value observed
  unfold deepWriterFunctional at observed
  cases found : term.head with
  | returned result =>
      simp [found] at observed
      obtain ⟨rfl, rfl⟩ := observed
      have source := Comp.head_returned_sound found
      subst term
      exact .returned
  | internal next =>
      simp only [found] at observed
      obtain ⟨step⟩ := Comp.head_internal_sound found
      exact .internal step (sound next log value observed)
  | base request =>
      by_cases selected : request.operation = 0
      · simp only [found, selected, if_pos, Option.map_eq_some_iff] at observed
        obtain ⟨tail, tailObserved, transformed⟩ := observed
        obtain ⟨rfl, rfl⟩ := transformed
        exact .tell (Comp.head_base_sound found) selected
          (sound (request.resume .unit) tail.1 tail.2 tailObserved)
      · simp [found, selected] at observed
  | free request =>
      by_cases same : request.interface = interface
      · cases clauseFound : handler.lookup request.operation with
        | none => simp [found, same, clauseFound] at observed
        | some clause =>
            simp only [found, same, if_pos, clauseFound] at observed
            exact .matched (Comp.head_free_sound found) same clauseFound
              (sound (request.answerWith clause) log value observed)
      · simp [found, same] at observed
  | stuck => simp [found] at observed

theorem deepWriterLimit_run_sound :
    DeepWriterSatisfies
      (fun term log value => DeepWriterRuns interface handler term log value)
      (deepWriterLimitFamily interface handler) :=
  deepWriterLimit_satisfies deepWriterRuns_oneLayer

end EffectSemantics
