import EffectSemantics.Operational.TypedWriterEvaluation

namespace EffectSemantics.TypedWriterTree

/-- Typed semantic affine clauses.  The signature lookup selects both the
parameter carrier and the response carrier. -/
structure AffineSemantics (sig : Signature) where
  clause : ∀ (interface operation : Nat) {parameterTy responseTy : Ty},
    sig.free interface operation = some ⟨parameterTy, responseTy⟩ →
    Option (ClosedVal sig parameterTy →
      TypedWriterTree sig (ClosedVal sig responseTy))

def shallow (selected : Nat) (handler : AffineSemantics sig) :
    TypedWriterTree sig α → TypedWriterTree sig α
  | .ret value => .ret value
  | .tell message next => .tell message (shallow selected handler next)
  | .free interface operation lookup parameter continuation =>
      if _same : interface = selected then
        match handler.clause interface operation lookup with
        | some response => (response parameter).bind continuation
        | none => .free interface operation lookup parameter (fun value =>
            shallow selected handler (continuation value))
      else
        .free interface operation lookup parameter (fun value =>
          shallow selected handler (continuation value))

theorem shallow_match (handler : AffineSemantics sig)
    (found : handler.clause interface operation lookup = some response) :
    shallow interface handler
      (.free interface operation lookup parameter continuation) =
      (response parameter).bind continuation := by
  simp [shallow, found]

theorem shallow_forward_other (different : interface ≠ selected) :
    shallow selected handler
      (.free interface operation lookup parameter continuation) =
      .free interface operation lookup parameter (fun value =>
        shallow selected handler (continuation value)) := by
  simp [shallow, different]

theorem shallow_forward_missing
    (missing : handler.clause interface operation lookup = none) :
    shallow interface handler
      (.free interface operation lookup parameter continuation) =
      .free interface operation lookup parameter (fun value =>
        shallow interface handler (continuation value)) := by
  simp [shallow, missing]

inductive Rel (relation : α → β → Prop) :
    TypedWriterTree sig α → TypedWriterTree sig β → Prop where
  | ret : relation left right → Rel relation (.ret left) (.ret right)
  | tell : Rel relation left right →
      Rel relation (.tell message left) (.tell message right)
  | free : (∀ response, Rel relation (left response) (right response)) →
      Rel relation (.free interface operation lookup parameter left)
        (.free interface operation lookup parameter right)

theorem Rel.reflEq (tree : TypedWriterTree sig α) : Rel (· = ·) tree tree := by
  induction tree with
  | ret value => exact .ret rfl
  | tell message next ih => exact .tell ih
  | free interface operation lookup parameter continuation ih => exact .free ih

theorem Rel.bind
    (treeRelation : Rel relation left right)
    (nextRelation : ∀ {a b}, relation a b →
      Rel resultRelation (leftNext a) (rightNext b)) :
    Rel resultRelation (left.bind leftNext) (right.bind rightNext) := by
  induction treeRelation with
  | ret related => exact nextRelation related
  | tell related ih => exact .tell ih
  | free related ih => exact .free ih

theorem Rel.graphMap (function : α → β) (tree : TypedWriterTree sig α) :
    Rel (fun left right => function left = right) tree (map function tree) := by
  induction tree with
  | ret value => exact .ret rfl
  | tell message next ih => exact .tell ih
  | free interface operation lookup parameter continuation ih => exact .free ih

theorem Rel.shallow
    {sig : Signature} {α β : Type} {relation : α → β → Prop}
    {left : TypedWriterTree sig α} {right : TypedWriterTree sig β}
    (treeRelation : Rel relation left right)
    (selected : Nat) (handler : AffineSemantics sig) :
    Rel relation (TypedWriterTree.shallow selected handler left)
      (TypedWriterTree.shallow selected handler right) := by
  induction treeRelation with
  | ret related => exact .ret related
  | tell related ih => exact .tell ih
  | free related ih =>
      rename_i responseTy leftContinuation rightContinuation interface operation
        parameterTy lookup parameter
      by_cases same : interface = selected
      · subst selected
        cases found : handler.clause interface operation lookup with
        | none =>
            rw [shallow_forward_missing found, shallow_forward_missing found]
            exact .free ih
        | some response =>
            rw [shallow_match handler found, shallow_match handler found]
            apply Rel.bind (Rel.reflEq (response parameter))
            intro leftValue rightValue equal
            subst rightValue
            exact related leftValue
      · rw [shallow_forward_other same, shallow_forward_other same]
        exact .free ih

theorem shallow_map (function : α → β) (tree : TypedWriterTree sig α) :
    map function (shallow selected handler tree) =
      shallow selected handler (map function tree) := by
  induction tree with
  | ret value => rfl
  | tell message next ih =>
      change TypedWriterTree.tell message
          (map function (shallow selected handler next)) =
        TypedWriterTree.tell message
          (shallow selected handler (map function next))
      exact congrArg (TypedWriterTree.tell message) ih
  | free interface operation lookup parameter continuation ih =>
      by_cases same : interface = selected
      · subst selected
        cases found : handler.clause interface operation lookup with
        | none =>
            rw [shallow_forward_missing found]
            simp only [map, bind]
            rw [shallow_forward_missing found]
            congr
            funext response
            exact ih response
        | some response =>
            rw [shallow_match handler found]
            simp only [map, bind_assoc, bind]
            rw [shallow_match handler found]
      · rw [shallow_forward_other same]
        simp only [map, bind]
        rw [shallow_forward_other same]
        congr
        funext response
        exact ih response

def replaceFirst (selected : Nat) (replacement : Effect) : Effect → Effect
  | [] => []
  | atom :: tail =>
      if atom = EffectAtom.free selected then replacement ++ tail
      else atom :: replaceFirst selected replacement tail

/-- Exact first-occurrence replacement under a prefix known not to contain
the selected interface. -/
theorem replaceFirst_anchored
    (freeOf : Effect.FreeOf selected pre) :
    replaceFirst selected replacement
      (pre ++ EffectAtom.free selected :: suffix) =
      pre ++ replacement ++ suffix := by
  induction pre with
  | nil => simp [replaceFirst]
  | cons atom tail ih =>
      simp only [Effect.FreeOf, List.mem_cons, not_or] at freeOf
      have atomNotSelected : atom ≠ EffectAtom.free selected := by
        intro equal
        exact freeOf.1 equal.symm
      simp [replaceFirst, atomNotSelected, ih freeOf.2, List.append_assoc]

/-- First-occurrence replacement is not monotone for ordered-subsequence
subeffecting.  This checked counterexample is why the exact-grade theorem below
cannot be lifted through arbitrary weakening without a monotone envelope or a
principal-grade restriction. -/
theorem replaceFirst_not_monotone :
    let lower := [EffectAtom.base 0, EffectAtom.free 0]
    let upper := [EffectAtom.free 0, EffectAtom.base 0, EffectAtom.free 0]
    lower ≤ upper ∧
      ¬replaceFirst 0 [EffectAtom.base 1] lower ≤
        replaceFirst 0 [EffectAtom.base 1] upper := by
  dsimp
  constructor
  · exact List.Sublist.cons _ (List.Sublist.refl _)
  · intro transformed
    change List.Sublist [EffectAtom.base 0, EffectAtom.base 1]
      [EffectAtom.base 1, EffectAtom.base 0, EffectAtom.free 0] at transformed
    have checked : [EffectAtom.base 0, EffectAtom.base 1].isSublist
        [EffectAtom.base 1, EffectAtom.base 0, EffectAtom.free 0] :=
      List.isSublist_iff_sublist.mpr transformed
    have computed : [EffectAtom.base 0, EffectAtom.base 1].isSublist
        [EffectAtom.base 1, EffectAtom.base 0, EffectAtom.free 0] = false := by
      decide
    rw [computed] at checked
    contradiction

/-- A finite word that over-approximates first replacement for every subword
of the given upper bound.  It is deliberately coarse; it records one concrete
way to recover soundness after naive replacement loses monotonicity. -/
def replacementEnvelope (selected : Nat) (replacement : Effect) :
    Effect → Effect
  | [] => []
  | atom :: tail =>
      if atom = EffectAtom.free selected then
        replacementEnvelope selected replacement tail ++ replacement ++ tail
      else atom :: replacementEnvelope selected replacement tail

theorem replaceFirst_le_envelope
    (factor : List.Sublist lower upper) :
    List.Sublist (replaceFirst selected replacement lower)
      (replacementEnvelope selected replacement upper) := by
  induction factor with
  | slnil => exact .slnil
  | cons atom factor ih =>
      by_cases selectedAtom : atom = EffectAtom.free selected
      · simp only [replacementEnvelope, selectedAtom, ↓reduceIte]
        exact List.sublist_append_of_sublist_left
          (List.sublist_append_of_sublist_left ih)
      · simp only [replacementEnvelope, selectedAtom, ↓reduceIte]
        exact List.Sublist.cons _ ih
  | cons_cons atom factor ih =>
      by_cases selectedAtom : atom = EffectAtom.free selected
      · subst atom
        simp only [replaceFirst, replacementEnvelope, ↓reduceIte]
        have body := List.Sublist.append (List.Sublist.refl replacement) factor
        apply body.trans
        simpa only [List.append_assoc] using
          (List.sublist_append_of_sublist_right (List.Sublist.refl _))
      · simp only [replaceFirst, replacementEnvelope, selectedAtom, ↓reduceIte]
        exact List.Sublist.cons_cons _ ih

/-- Exact (unweakened) grade derivations, used to state the structural effect
equation before proving any monotonicity through subeffecting. -/
inductive ExactEffect : TypedWriterTree sig α → Effect → Type where
  | ret : ExactEffect (.ret value) 1
  | tell : ExactEffect tree effect →
      ExactEffect (.tell message tree) ([EffectAtom.base 0] * effect)
  | free : (∀ response, ExactEffect (continuation response) effect) →
      ExactEffect (.free interface operation lookup parameter continuation)
        ([EffectAtom.free interface] * effect)

noncomputable def ExactEffect.toHasEffect
    (typing : ExactEffect tree effect) : HasEffect tree effect := by
  induction typing with
  | ret => exact .ret
  | tell tail ih => exact .tell ih
  | free continuation ih => exact .free ih

/-- Exhaustive semantic clauses with a uniform response grade. -/
structure ClauseEffectWitness (handler : AffineSemantics sig)
    (selected operation : Nat) {parameterTy responseTy : Ty}
    (lookup : sig.free selected operation =
      some ⟨parameterTy, responseTy⟩) (replacement : Effect) where
  clause : ClosedVal sig parameterTy →
    TypedWriterTree sig (ClosedVal sig responseTy)
  found : handler.clause selected operation lookup = some clause
  typing : ∀ parameter, HasEffect (clause parameter) replacement

structure ExhaustiveEffect (selected : Nat) (handler : AffineSemantics sig)
    (replacement : Effect) where
  response : ∀ (operation : Nat) {parameterTy responseTy : Ty}
      (lookup : sig.free selected operation =
        some ⟨parameterTy, responseTy⟩),
    ClauseEffectWitness handler selected operation lookup replacement

/-- On exact grades an exhaustive typed shallow handler replaces precisely the
first selected interface atom. Matching uses the bare continuation; all prior
Writer and other-interface nodes are rebuilt recursively. -/
noncomputable def ExactEffect.shallow
    (typing : ExactEffect tree effect)
    (package : ExhaustiveEffect selected handler replacement) :
    HasEffect (TypedWriterTree.shallow selected handler tree)
      (replaceFirst selected replacement effect) := by
  induction typing with
  | ret => exact .ret
  | tell tailTyping ih =>
      exact HasEffect.tell ih
  | free continuationTyping ih =>
      rename_i responseTy continuation interface operation parameterTy lookup
        parameter
      by_cases same : interface = selected
      · subst selected
        let witness := package.response operation lookup
        rw [TypedWriterTree.shallow_match handler witness.found]
        simpa [replaceFirst] using
          (witness.typing parameter).bind (fun response =>
            (continuationTyping response).toHasEffect)
      · rw [TypedWriterTree.shallow_forward_other same]
        simpa [replaceFirst, same] using
          HasEffect.free ih

end EffectSemantics.TypedWriterTree
