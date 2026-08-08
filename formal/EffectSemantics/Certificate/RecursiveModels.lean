import EffectSemantics.Recursive.DeepStateBoundary

namespace EffectSemantics

/-- Minimal reusable certificate for a deterministic finite-boundary model of
the recursive calculus.  Completion and determinism are derived, not fields. -/
structure RecursiveBoundaryCert (Outcome : Type) where
  observe : Nat → Comp → Option Outcome
  stable : ∀ {fuel term outcome}, observe fuel term = some outcome →
    observe (fuel + 1) term = some outcome
  Runs : Comp → Outcome → Prop
  finiteAdequacy : ∀ {term outcome},
    Runs term outcome ↔ ∃ fuel, observe fuel term = some outcome

namespace RecursiveBoundaryCert

def observation (cert : RecursiveBoundaryCert Outcome) (term : Comp) :
    StableObservation Outcome where
  observeAt fuel := cert.observe fuel term
  stable := cert.stable

noncomputable def limit (cert : RecursiveBoundaryCert Outcome) (term : Comp) :
    Option Outcome := (cert.observation term).limitOutcome

theorem limit_adequacy (cert : RecursiveBoundaryCert Outcome) :
    cert.Runs term outcome ↔ cert.limit term = some outcome := by
  rw [cert.finiteAdequacy]
  constructor
  · rintro ⟨fuel, observed⟩
    exact StableObservation.limitOutcome_of_observed _ observed
  · intro observed
    exact StableObservation.limitOutcome_some_witness _ observed

theorem runs_deterministic (cert : RecursiveBoundaryCert Outcome)
    (first : cert.Runs term left) (second : cert.Runs term right) :
    left = right := by
  have leftObserved := cert.limit_adequacy.mp first
  have rightObserved := cert.limit_adequacy.mp second
  rw [leftObserved] at rightObserved
  exact Option.some.inj rightObserved

theorem limit_none_iff (cert : RecursiveBoundaryCert Outcome) :
    cert.limit term = none ↔ ¬ ∃ outcome, cert.Runs term outcome := by
  constructor
  · intro absent ⟨outcome, runs⟩
    have observed := cert.limit_adequacy.mp runs
    rw [absent] at observed
    cases observed
  · intro noRun
    cases found : cert.limit term with
    | none => rfl
    | some outcome =>
        exact False.elim (noRun ⟨outcome, cert.limit_adequacy.mpr found⟩)

end RecursiveBoundaryCert

def recursiveWriterBoundaryCert (interface : Nat) (handler : AffineHandler) :
    RecursiveBoundaryCert DeepWriterBoundary where
  observe fuel term := term.observeDeepWriterBoundary fuel interface handler
  stable := Comp.observeDeepWriterBoundary_succ_of_some
  Runs term boundary := DeepWriterBoundaryRuns interface handler term boundary
  finiteAdequacy := deep_writer_boundary_finite_adequacy

def recursiveExceptionBoundaryCert (interface : Nat)
    (handler : AffineHandler) : RecursiveBoundaryCert DeepExceptionBoundary where
  observe fuel term := term.observeDeepExceptionBoundary fuel interface handler
  stable := Comp.observeDeepExceptionBoundary_succ_of_some
  Runs term boundary := DeepExceptionBoundaryRuns interface handler term boundary
  finiteAdequacy := by
    intro term outcome
    constructor
    · exact DeepExceptionBoundaryRuns.to_observation
    · rintro ⟨fuel, observed⟩
      exact Comp.observeDeepExceptionBoundary_reflects observed

def recursiveStateBoundaryCert (interface : Nat) (handler : AffineHandler)
    (initialState : Bool) : RecursiveBoundaryCert DeepStateBoundary where
  observe fuel term :=
    term.observeDeepStateBoundary fuel interface handler initialState
  stable := Comp.observeDeepStateBoundary_succ_of_some
  Runs term boundary :=
    DeepStateBoundaryRuns interface handler term initialState boundary
  finiteAdequacy := by
    intro term outcome
    constructor
    · exact DeepStateBoundaryRuns.to_observation
    · rintro ⟨fuel, observed⟩
      exact Comp.observeDeepStateBoundary_reflects observed

theorem recursiveWriterBoundaryCert_limit_eq
    (interface : Nat) (handler : AffineHandler) (term : Comp) :
    (recursiveWriterBoundaryCert interface handler).limit term =
      term.deepWriterBoundaryLimit interface handler := by
  rw [Comp.deepWriterBoundaryLimit_eq_generic]
  rfl

theorem recursiveExceptionBoundaryCert_limit_eq
    (interface : Nat) (handler : AffineHandler) (term : Comp) :
    (recursiveExceptionBoundaryCert interface handler).limit term =
      term.deepExceptionBoundaryLimit interface handler := rfl

theorem recursiveStateBoundaryCert_limit_eq
    (interface : Nat) (handler : AffineHandler) (state : Bool) (term : Comp) :
    (recursiveStateBoundaryCert interface handler state).limit term =
      term.deepStateBoundaryLimit interface handler state := rfl

end EffectSemantics
