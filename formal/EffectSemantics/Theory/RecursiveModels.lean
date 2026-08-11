import EffectSemantics.Recursive.DeepStateBoundary

namespace EffectSemantics

/-- Minimal reusable package for a deterministic finite-boundary model of
the recursive calculus.  Completion and determinism are derived, not fields. -/
structure RecursiveBoundaryModel (Outcome : Type) where
  observe : Nat → Comp → Option Outcome
  stable : ∀ {fuel term outcome}, observe fuel term = some outcome →
    observe (fuel + 1) term = some outcome
  Runs : Comp → Outcome → Prop
  finiteAdequacy : ∀ {term outcome},
    Runs term outcome ↔ ∃ fuel, observe fuel term = some outcome

namespace RecursiveBoundaryModel

def observation (cert : RecursiveBoundaryModel Outcome) (term : Comp) :
    StableObservation Outcome where
  observeAt fuel := cert.observe fuel term
  stable := cert.stable

noncomputable def limit (cert : RecursiveBoundaryModel Outcome) (term : Comp) :
    Option Outcome := (cert.observation term).limitOutcome

theorem limit_adequacy (cert : RecursiveBoundaryModel Outcome) :
    cert.Runs term outcome ↔ cert.limit term = some outcome := by
  rw [cert.finiteAdequacy]
  constructor
  · rintro ⟨fuel, observed⟩
    exact StableObservation.limitOutcome_of_observed _ observed
  · intro observed
    exact StableObservation.limitOutcome_some_witness _ observed

theorem runs_deterministic (cert : RecursiveBoundaryModel Outcome)
    (first : cert.Runs term left) (second : cert.Runs term right) :
    left = right := by
  have leftObserved := cert.limit_adequacy.mp first
  have rightObserved := cert.limit_adequacy.mp second
  rw [leftObserved] at rightObserved
  exact Option.some.inj rightObserved

theorem limit_none_iff (cert : RecursiveBoundaryModel Outcome) :
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

end RecursiveBoundaryModel

def recursiveWriterBoundaryModel (interface : Nat) (handler : AffineHandler) :
    RecursiveBoundaryModel DeepWriterBoundary where
  observe fuel term := term.observeDeepWriterBoundary fuel interface handler
  stable := Comp.observeDeepWriterBoundary_succ_of_some
  Runs term boundary := DeepWriterBoundaryRuns interface handler term boundary
  finiteAdequacy := deep_writer_boundary_finite_adequacy

def recursiveExceptionBoundaryModel (interface : Nat)
    (handler : AffineHandler) : RecursiveBoundaryModel DeepExceptionBoundary where
  observe fuel term := term.observeDeepExceptionBoundary fuel interface handler
  stable := Comp.observeDeepExceptionBoundary_succ_of_some
  Runs term boundary := DeepExceptionBoundaryRuns interface handler term boundary
  finiteAdequacy := by
    intro term outcome
    constructor
    · exact DeepExceptionBoundaryRuns.to_observation
    · rintro ⟨fuel, observed⟩
      exact Comp.observeDeepExceptionBoundary_reflects observed

def recursiveStateBoundaryModel (interface : Nat) (handler : AffineHandler)
    (initialState : Bool) : RecursiveBoundaryModel DeepStateBoundary where
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

theorem recursiveWriterBoundaryModel_limit_eq
    (interface : Nat) (handler : AffineHandler) (term : Comp) :
    (recursiveWriterBoundaryModel interface handler).limit term =
      term.deepWriterBoundaryLimit interface handler := by
  rw [Comp.deepWriterBoundaryLimit_eq_generic]
  rfl

theorem recursiveExceptionBoundaryModel_limit_eq
    (interface : Nat) (handler : AffineHandler) (term : Comp) :
    (recursiveExceptionBoundaryModel interface handler).limit term =
      term.deepExceptionBoundaryLimit interface handler := rfl

theorem recursiveStateBoundaryModel_limit_eq
    (interface : Nat) (handler : AffineHandler) (state : Bool) (term : Comp) :
    (recursiveStateBoundaryModel interface handler state).limit term =
      term.deepStateBoundaryLimit interface handler state := rfl

/-- Optional refinement recording exactly the premises under which a selected
interface cannot occur at an outward boundary. -/
structure RecursiveDischarge (base : RecursiveBoundaryModel Outcome)
    (selected : Nat) where
  freeInterface : Outcome → Option Nat
  Good : Comp → Prop
  discharge : ∀ {term outcome}, Good term →
    base.limit term = some outcome → freeInterface outcome ≠ some selected

def DeepWriterBoundary.freeInterface : DeepWriterBoundary → Option Nat
  | .free _ request => some request.interface
  | _ => none

def DeepExceptionBoundary.freeInterface : DeepExceptionBoundary → Option Nat
  | .free request => some request.interface
  | _ => none

def DeepStateBoundary.freeInterface : DeepStateBoundary → Option Nat
  | .free request _ => some request.interface
  | _ => none

def recursiveWriterDischarge
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (exhaustive : handler.Exhaustive sig interface)
    (writerUnit : WriterResponseUnit sig) :
    RecursiveDischarge (recursiveWriterBoundaryModel interface handler)
      interface where
  freeInterface := DeepWriterBoundary.freeInterface
  Good term := ∃ resultTy effect,
    Nonempty (HasComp sig [] term resultTy effect)
  discharge := by
    intro term outcome good observed
    obtain ⟨resultTy, effect, ⟨typing⟩⟩ := good
    rw [recursiveWriterBoundaryModel_limit_eq] at observed
    cases outcome with
    | returned => simp [DeepWriterBoundary.freeInterface]
    | base => simp [DeepWriterBoundary.freeInterface]
    | free log request =>
        simp only [DeepWriterBoundary.freeInterface, ne_eq,
          Option.some.injEq]
        exact deepWriterBoundaryLimit_discharges typing handlerTyping exhaustive
          writerUnit observed

def recursiveExceptionDischarge
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (exhaustive : handler.Exhaustive sig interface) :
    RecursiveDischarge (recursiveExceptionBoundaryModel interface handler)
      interface where
  freeInterface := DeepExceptionBoundary.freeInterface
  Good term := ∃ resultTy effect,
    Nonempty (HasComp sig [] term resultTy effect)
  discharge := by
    intro term outcome good observed
    obtain ⟨resultTy, effect, ⟨typing⟩⟩ := good
    rw [recursiveExceptionBoundaryModel_limit_eq] at observed
    cases outcome with
    | returned => simp [DeepExceptionBoundary.freeInterface]
    | raised => simp [DeepExceptionBoundary.freeInterface]
    | base => simp [DeepExceptionBoundary.freeInterface]
    | free request =>
        simp only [DeepExceptionBoundary.freeInterface, ne_eq,
          Option.some.injEq]
        exact deep_exception_boundary_limit_discharges typing handlerTyping
          exhaustive observed

def recursiveStateDischarge
    (handlerTyping : HasAffineHandler sig [] interface handler clauseEffect)
    (exhaustive : handler.Exhaustive sig interface)
    (stateLaws : StateResponseLaws sig) (state : Bool) :
    RecursiveDischarge
      (recursiveStateBoundaryModel interface handler state) interface where
  freeInterface := DeepStateBoundary.freeInterface
  Good term := ∃ resultTy effect,
    Nonempty (HasComp sig [] term resultTy effect)
  discharge := by
    intro term outcome good observed
    obtain ⟨resultTy, effect, ⟨typing⟩⟩ := good
    rw [recursiveStateBoundaryModel_limit_eq] at observed
    cases outcome with
    | returned => simp [DeepStateBoundary.freeInterface]
    | base => simp [DeepStateBoundary.freeInterface]
    | free request finalState =>
        simp only [DeepStateBoundary.freeInterface, ne_eq,
          Option.some.injEq]
        exact deep_state_boundary_limit_discharges typing handlerTyping
          exhaustive stateLaws observed

end EffectSemantics
