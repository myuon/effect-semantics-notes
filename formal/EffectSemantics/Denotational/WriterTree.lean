import EffectSemantics.Operational.ShallowHandler

namespace EffectSemantics

/-- Concrete finite Writer/free tree. Writer requests have deterministic unit
responses; user-defined requests retain value-indexed continuations. -/
inductive WriterTree (α : Type) where
  | ret (value : α)
  | tell (message : Val) (next : WriterTree α)
  | free (interface operation : Nat) (parameter : Val)
      (continuation : Val → WriterTree α)

namespace WriterTree

def bind (tree : WriterTree α) (next : α → WriterTree β) : WriterTree β :=
  match tree with
  | .ret value => next value
  | .tell message tail => .tell message (tail.bind next)
  | .free interface operation parameter continuation =>
      .free interface operation parameter (fun response =>
        (continuation response).bind next)

def map (function : α → β) (tree : WriterTree α) : WriterTree β :=
  tree.bind (fun value => .ret (function value))

@[simp] theorem ret_bind (value : α) (next : α → WriterTree β) :
    (ret value).bind next = next value := rfl

@[simp] theorem tell_bind (message : Val) (tree : WriterTree α)
    (next : α → WriterTree β) :
    (tell message tree).bind next = tell message (tree.bind next) := rfl

@[simp] theorem free_bind (interface operation : Nat) (parameter : Val)
    (continuation : Val → WriterTree α) (next : α → WriterTree β) :
    (free interface operation parameter continuation).bind next =
      free interface operation parameter (fun response =>
        (continuation response).bind next) := rfl

theorem bind_ret (tree : WriterTree α) :
    tree.bind ret = tree := by
  induction tree with
  | ret => rfl
  | tell message tail ih => simp [bind, ih]
  | free interface operation parameter continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response

theorem bind_assoc (tree : WriterTree α) (f : α → WriterTree β)
    (g : β → WriterTree γ) :
    (tree.bind f).bind g = tree.bind (fun value => (f value).bind g) := by
  induction tree with
  | ret => rfl
  | tell message tail ih => simp [bind, ih]
  | free interface operation parameter continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response

theorem map_id (tree : WriterTree α) : map id tree = tree := by
  simpa [map] using bind_ret tree

theorem map_comp (first : α → β) (second : β → γ)
    (tree : WriterTree α) :
    map second (map first tree) = map (second ∘ first) tree := by
  rw [map, map, bind_assoc]
  rfl

theorem map_bind (function : β → γ) (tree : WriterTree α)
    (next : α → WriterTree β) :
    map function (tree.bind next) =
      tree.bind (fun value => map function (next value)) := by
  simp only [map, bind_assoc]

/-- Semantic affine clauses return one operation response tree. -/
structure AffineSemantics where
  clause : Nat → Option (Val → WriterTree Val)

def shallow (selected : Nat) (handler : AffineSemantics) :
    WriterTree α → WriterTree α
  | .ret value => .ret value
  | .tell message next => .tell message (shallow selected handler next)
  | .free interface operation parameter continuation =>
      if _same : interface = selected then
        match handler.clause operation with
        | some response => (response parameter).bind continuation
        | none => .free interface operation parameter (fun value =>
            shallow selected handler (continuation value))
      else
        .free interface operation parameter (fun value =>
          shallow selected handler (continuation value))

@[simp] theorem shallow_ret (selected : Nat) (handler : AffineSemantics)
    (value : α) : shallow selected handler (.ret value) = .ret value := rfl

@[simp] theorem shallow_tell (selected : Nat) (handler : AffineSemantics)
    (message : Val) (next : WriterTree α) :
    shallow selected handler (.tell message next) =
      .tell message (shallow selected handler next) := rfl

theorem shallow_match (handler : AffineSemantics)
    (found : handler.clause operation = some response) :
    shallow interface handler
      (.free interface operation parameter continuation) =
      (response parameter).bind continuation := by
  simp [shallow, found]

theorem shallow_forward_other (different : interface ≠ selected) :
    shallow selected handler
      (.free interface operation parameter continuation) =
      .free interface operation parameter (fun value =>
        shallow selected handler (continuation value)) := by
  simp [shallow, different]

theorem shallow_forward_missing
    (missing : handler.clause operation = none) :
    shallow interface handler
      (.free interface operation parameter continuation) =
      .free interface operation parameter (fun value =>
        shallow interface handler (continuation value)) := by
  simp [shallow, missing]

/-- Writer observation of a fully handled tree. -/
def runClosed : WriterTree α → Option (List Val × α)
  | .ret value => some ([], value)
  | .tell message next =>
      (runClosed next).map (fun result => (message :: result.1, result.2))
  | .free _ _ _ _ => none

/-- Structural lifting of a relation through Writer/free trees. -/
inductive Rel (relation : α → β → Prop) : WriterTree α → WriterTree β → Prop where
  | ret : relation left right → Rel relation (.ret left) (.ret right)
  | tell : Rel relation left right →
      Rel relation (.tell message left) (.tell message right)
  | free : (∀ response, Rel relation (left response) (right response)) →
      Rel relation (.free interface operation parameter left)
        (.free interface operation parameter right)

theorem Rel.reflEq (tree : WriterTree α) : Rel (· = ·) tree tree := by
  induction tree with
  | ret value => exact .ret rfl
  | tell message next ih => exact .tell ih
  | free interface operation parameter continuation ih => exact .free ih

/-- Mapping is precisely the lifting of the graph of the result function. -/
theorem Rel.graphMap (function : α → β) (tree : WriterTree α) :
    Rel (fun left right => function left = right) tree (map function tree) := by
  induction tree with
  | ret value => exact .ret rfl
  | tell message next ih => exact .tell ih
  | free interface operation parameter continuation ih => exact .free ih

theorem Rel.bind
    (treeRelation : Rel relation left right)
    (nextRelation : ∀ {a b}, relation a b →
      Rel resultRelation (leftNext a) (rightNext b)) :
    Rel resultRelation (left.bind leftNext) (right.bind rightNext) := by
  induction treeRelation with
  | ret related => exact nextRelation related
  | tell related ih => exact .tell ih
  | free related ih => exact .free ih

/-- A fixed semantic handler preserves every structural result relation.  In
the matching case its response tree is related to itself and the bare
continuations are related pointwise; forwarding follows the induction
hypothesis instead. -/
theorem Rel.shallow (treeRelation : Rel relation left right)
    (selected : Nat) (handler : AffineSemantics) :
    Rel relation (shallow selected handler left)
      (shallow selected handler right) := by
  induction treeRelation with
  | ret related => exact .ret related
  | tell related ih => exact .tell ih
  | free related ih =>
      rename_i leftContinuation rightContinuation interface operation parameter
      by_cases same : interface = selected
      · subst selected
        cases found : handler.clause operation with
        | none =>
            rw [shallow_forward_missing found, shallow_forward_missing found]
            exact .free ih
        | some response =>
            rw [shallow_match handler found, shallow_match handler found]
            apply Rel.bind (Rel.reflEq (response parameter))
            intro a b equal
            subst b
            exact related a
      · rw [shallow_forward_other same, shallow_forward_other same]
        exact .free ih

/-- Shallow handling is natural in the result carrier.  This is the concrete
Writer/free-tree instance of morphism lifting. -/
theorem shallow_map (function : α → β) (tree : WriterTree α) :
    map function (shallow selected handler tree) =
      shallow selected handler (map function tree) := by
  induction tree with
  | ret value => rfl
  | tell message next ih =>
      change WriterTree.tell message
          (map function (shallow selected handler next)) =
        WriterTree.tell message
          (shallow selected handler (map function next))
      exact congrArg (WriterTree.tell message) ih
  | free interface operation parameter continuation ih =>
      by_cases same : interface = selected
      · subst selected
        cases found : handler.clause operation with
        | none =>
            rw [shallow_forward_missing found]
            simp only [map, free_bind]
            rw [shallow_forward_missing found]
            congr
            funext response
            exact ih response
        | some response =>
            rw [shallow_match handler found]
            simp only [map, bind_assoc, free_bind]
            rw [shallow_match handler found]
      · rw [shallow_forward_other same]
        simp only [map, free_bind]
        rw [shallow_forward_other same]
        congr
        funext response
        exact ih response

/-- Inductive ground observation, equivalent to successful `runClosed` but
better suited to adequacy induction. -/
inductive Observes : WriterTree α → List Val → α → Prop where
  | ret : Observes (.ret value) [] value
  | tell : Observes tree log value →
      Observes (.tell message tree) (message :: log) value

/-- Closed Writer observations reflect the lifted result relation. -/
theorem Rel.observes
    (treeRelation : Rel relation left right)
    (observed : Observes left log leftValue) :
    ∃ rightValue, Observes right log rightValue ∧
      relation leftValue rightValue := by
  induction treeRelation generalizing log leftValue with
  | ret related =>
      cases observed
      exact ⟨_, .ret, related⟩
  | tell related ih =>
      cases observed with
      | tell tailObserved =>
          obtain ⟨rightValue, rightObserved, valueRelated⟩ := ih tailObserved
          exact ⟨rightValue, .tell rightObserved, valueRelated⟩
  | free related ih => cases observed

end WriterTree
end EffectSemantics
