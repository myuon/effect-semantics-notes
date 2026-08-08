import EffectSemantics.Recursive.FiniteObservation
import EffectSemantics.Operational.WriterEvaluation

namespace EffectSemantics

inductive WriterFiniteOutcome where
  | returned (log : List Val) (value : Val)
  | base (log : List Val) (request : BaseRequest)
  | free (log : List Val) (request : FreeRequest)
  deriving DecidableEq, Repr

def WriterFiniteOutcome.prepend (messages : List Val) :
    WriterFiniteOutcome → WriterFiniteOutcome
  | .returned log value => .returned (messages ++ log) value
  | .base log request => .base (messages ++ log) request
  | .free log request => .free (messages ++ log) request

/-- Fuel-indexed recursive Writer observation. Base operation zero is `tell`:
it emits its parameter, receives unit, and evaluation continues. -/
def Comp.observeWriter : Nat → Comp → Option WriterFiniteOutcome
  | 0, _ => none
  | fuel + 1, term =>
      match term.head with
      | .returned value => some (.returned [] value)
      | .internal next => next.observeWriter fuel
      | .base request =>
          if request.operation = 0 then
            (request.resume .unit).observeWriter fuel |>.map
              (WriterFiniteOutcome.prepend [request.parameter])
          else
            some (.base [] request)
      | .free request => some (.free [] request)
      | .stuck => none

@[simp] theorem Comp.observeWriter_zero (term : Comp) :
    term.observeWriter 0 = none := rfl

theorem Comp.observeWriter_succ_of_some
    {term : Comp} {fuel : Nat} {outcome : WriterFiniteOutcome}
    (observed : term.observeWriter fuel = some outcome) :
    term.observeWriter (fuel + 1) = some outcome := by
  induction fuel generalizing term outcome with
  | zero => simp [Comp.observeWriter] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned value => simpa [Comp.observeWriter, found] using observed
      | internal next =>
          simp only [Comp.observeWriter, found] at observed ⊢
          exact ih observed
      | base request =>
          by_cases selected : request.operation = 0
          · simp only [Comp.observeWriter, found, selected, if_pos, Option.map_eq_some_iff]
              at observed ⊢
            obtain ⟨tail, tailObserved, transformed⟩ := observed
            exact ⟨tail, ih tailObserved, transformed⟩
          · simpa [Comp.observeWriter, found, selected] using observed
      | free request => simpa [Comp.observeWriter, found] using observed
      | stuck => simp [Comp.observeWriter, found] at observed

structure WriterPartialObservation where
  observeAt : Nat → Option WriterFiniteOutcome
  stable : ∀ {fuel outcome}, observeAt fuel = some outcome →
    observeAt (fuel + 1) = some outcome

def Comp.writerOperationalApprox (term : Comp) : WriterPartialObservation where
  observeAt fuel := term.observeWriter fuel
  stable := Comp.observeWriter_succ_of_some

def WriterPartialObservation.bottom : WriterPartialObservation where
  observeAt _ := none
  stable := by simp

@[ext] theorem WriterPartialObservation.ext
    {left right : WriterPartialObservation}
    (equal : left.observeAt = right.observeAt) : left = right := by
  cases left
  cases right
  cases equal
  rfl

theorem silentLoop_writer_bottom :
    silentLoop.writerOperationalApprox = WriterPartialObservation.bottom := by
  apply WriterPartialObservation.ext
  funext fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

def oneTell : Comp :=
  .letE (.baseOp 0 (.bool true)) (.ret .unit)

theorem oneTell_observation :
    oneTell.observeWriter 3 =
      some (.returned [.bool true] .unit) := rfl

/-- Every finite direct Writer run appears at some finite approximation. -/
theorem WriterRuns.to_observeWriter
    (runs : WriterRuns term log value) :
    ∃ fuel, term.observeWriter fuel = some (.returned log value) := by
  induction runs with
  | returned => exact ⟨1, rfl⟩
  | internal step runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      exact ⟨fuel + 1, by simp [Comp.observeWriter, step.to_head, observed]⟩
  | tell exposed selected runs ih =>
      obtain ⟨fuel, observed⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [exposed]
      simp [Comp.observeWriter, BaseRequest.source_head, selected, observed,
        WriterFiniteOutcome.prepend]

/-- A returned finite Writer projection reconstructs the direct operational
run, completing finite return/log reflection. -/
theorem Comp.observeWriter_return_reflects
    (observed : term.observeWriter fuel = some (.returned log value)) :
    WriterRuns term log value := by
  induction fuel generalizing term log value with
  | zero => simp [Comp.observeWriter] at observed
  | succ fuel ih =>
      cases found : term.head with
      | returned result =>
          simp [Comp.observeWriter, found] at observed
          obtain ⟨rfl, rfl⟩ := observed
          have source := Comp.head_returned_sound found
          subst term
          exact .returned
      | internal next =>
          simp only [Comp.observeWriter, found] at observed
          obtain ⟨step⟩ := Comp.head_internal_sound found
          exact .internal step (ih observed)
      | base request =>
          by_cases selected : request.operation = 0
          · simp only [Comp.observeWriter, found, selected, if_pos,
              Option.map_eq_some_iff] at observed
            obtain ⟨tail, tailObserved, transformed⟩ := observed
            cases tail with
            | returned tailLog tailValue =>
                simp [WriterFiniteOutcome.prepend] at transformed
                obtain ⟨rfl, rfl⟩ := transformed
                exact .tell (Comp.head_base_sound found) selected
                  (ih tailObserved)
            | base tailLog tailRequest =>
                simp [WriterFiniteOutcome.prepend] at transformed
            | free tailLog tailRequest =>
                simp [WriterFiniteOutcome.prepend] at transformed
          · simp [Comp.observeWriter, found, selected] at observed
      | free request => simp [Comp.observeWriter, found] at observed
      | stuck => simp [Comp.observeWriter, found] at observed

theorem ProducesWriterTree.observation_appears
    (produces : ProducesWriterTree term tree)
    (observes : WriterTree.Observes tree log value) :
    ∃ fuel, term.observeWriter fuel = some (.returned log value) :=
  (produces.sound observes).to_observeWriter

theorem writer_finite_return_adequacy :
    WriterRuns term log value ↔
      ∃ fuel, term.observeWriter fuel = some (.returned log value) :=
  ⟨WriterRuns.to_observeWriter,
    fun ⟨_fuel, observed⟩ => Comp.observeWriter_return_reflects observed⟩

end EffectSemantics
