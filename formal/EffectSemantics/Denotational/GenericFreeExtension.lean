namespace EffectSemantics

/-!
# Generic finite free-operation extension

This module constructs the finite carrier underlying the abstract extension
theorem.  Both old base effects and newly adjoined effects are presented by
typed operation signatures.  Keeping the old signature explicit records the
extra one-layer structure that is needed to extend an arbitrary monad.
-/

/-- A typed algebraic-operation signature.  Parameters may be included in
`Op`; `Response op` is the type returned to the continuation. -/
structure OperationSignature where
  Op : Type
  Response : Op → Type

/-- The empty operation signature. -/
def OperationSignature.empty : OperationSignature where
  Op := Empty
  Response := Empty.elim

/-- Finite trees containing old base operations and newly adjoined free
operations. -/
inductive FreeExtension (base free : OperationSignature) (α : Type) where
  | ret (value : α)
  | baseOp (operation : base.Op)
      (continuation : base.Response operation → FreeExtension base free α)
  | freeOp (operation : free.Op)
      (continuation : free.Response operation → FreeExtension base free α)

namespace FreeExtension

def bind (tree : FreeExtension base free α)
    (next : α → FreeExtension base free β) : FreeExtension base free β :=
  match tree with
  | .ret value => next value
  | .baseOp operation continuation =>
      .baseOp operation (fun response => (continuation response).bind next)
  | .freeOp operation continuation =>
      .freeOp operation (fun response => (continuation response).bind next)

def map (function : α → β) (tree : FreeExtension base free α) :
    FreeExtension base free β :=
  tree.bind (fun value => .ret (function value))

@[simp] theorem ret_bind (value : α)
    (next : α → FreeExtension base free β) :
    (ret value).bind next = next value := rfl

@[simp] theorem base_bind (operation : base.Op)
    (continuation : base.Response operation → FreeExtension base free α)
    (next : α → FreeExtension base free β) :
    (baseOp operation continuation).bind next =
      baseOp operation (fun response => (continuation response).bind next) := rfl

@[simp] theorem free_bind (operation : free.Op)
    (continuation : free.Response operation → FreeExtension base free α)
    (next : α → FreeExtension base free β) :
    (freeOp operation continuation).bind next =
      freeOp operation (fun response => (continuation response).bind next) := rfl

theorem bind_ret (tree : FreeExtension base free α) :
    tree.bind ret = tree := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response
  | freeOp operation continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response

theorem bind_assoc (tree : FreeExtension base free α)
    (first : α → FreeExtension base free β)
    (second : β → FreeExtension base free γ) :
    (tree.bind first).bind second =
      tree.bind (fun value => (first value).bind second) := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response
  | freeOp operation continuation ih =>
      simp only [bind]
      congr
      funext response
      exact ih response

theorem map_id (tree : FreeExtension base free α) : map id tree = tree := by
  simpa [map] using bind_ret tree

theorem map_comp (first : α → β) (second : β → γ)
    (tree : FreeExtension base free α) :
    map second (map first tree) = map (second ∘ first) tree := by
  rw [map, map, bind_assoc]
  rfl

theorem map_bind (function : β → γ) (tree : FreeExtension base free α)
    (next : α → FreeExtension base free β) :
    map function (tree.bind next) =
      tree.bind (fun value => map function (next value)) := by
  simp only [map, bind_assoc]

/-- The old base carrier, before adjoining any free operations. -/
abbrev BaseTree (base : OperationSignature) (α : Type) :=
  FreeExtension base OperationSignature.empty α

/-- Canonical embedding of the old base carrier into its free extension. -/
def embedBase : BaseTree base α → FreeExtension base free α
  | .ret value => .ret value
  | .baseOp operation continuation =>
      .baseOp operation (fun response => embedBase (continuation response))
  | .freeOp operation _ => Empty.elim operation

@[simp] theorem embedBase_ret (value : α) :
    embedBase (free := free) (.ret value : BaseTree base α) = .ret value := rfl

theorem embedBase_bind (tree : BaseTree base α)
    (next : α → BaseTree base β) :
    embedBase (free := free) (tree.bind next) =
      (embedBase (free := free) tree).bind
        (fun value => embedBase (free := free) (next value)) := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih =>
      simp only [bind, embedBase]
      congr
      funext response
      exact ih response
  | freeOp operation _ => exact Empty.elim operation

/-- A tree is old-language-only when it contains no newly adjoined request. -/
inductive BaseOnly : FreeExtension base free α → Type where
  | ret (value : α) : BaseOnly (.ret value)
  | baseOp (operation : base.Op)
      (continuation : base.Response operation → FreeExtension base free α) :
      (∀ response, BaseOnly (continuation response)) →
      BaseOnly (.baseOp operation continuation)

def embedBase_baseOnly (tree : BaseTree base α) :
    BaseOnly (embedBase (free := free) tree) :=
  match tree with
  | .ret value => .ret value
  | .baseOp operation continuation =>
      .baseOp operation _ (fun response => embedBase_baseOnly (continuation response))
  | .freeOp operation _ => Empty.elim operation

/-- Erasure is defined only with a proof that no new request occurs. -/
def eraseFree (tree : FreeExtension base free α) (old : tree.BaseOnly) :
    BaseTree base α :=
  match tree, old with
  | .ret value, .ret _ => .ret value
  | .baseOp operation continuation, .baseOp _ _ children =>
      .baseOp operation (fun response => eraseFree (continuation response) (children response))

theorem eraseFree_embedBase (tree : BaseTree base α) :
    eraseFree (embedBase (free := free) tree) (embedBase_baseOnly tree) = tree := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih =>
      simp only [embedBase, embedBase_baseOnly, eraseFree]
      congr
      funext response
      exact ih response
  | freeOp operation _ => exact Empty.elim operation

/-- A response-preserving map of typed operation signatures.  The response
map is contravariant because it transports the target continuation back to
the source response type. -/
structure SignatureMorphism (source target : OperationSignature) where
  onOp : source.Op → target.Op
  onResponse : ∀ operation, target.Response (onOp operation) → source.Response operation

def SignatureMorphism.id (sig : OperationSignature) : SignatureMorphism sig sig where
  onOp := fun operation => operation
  onResponse := fun _ value => value

def SignatureMorphism.comp (second : SignatureMorphism middle target)
    (first : SignatureMorphism source middle) : SignatureMorphism source target where
  onOp := second.onOp ∘ first.onOp
  onResponse := fun operation value => first.onResponse operation
    (second.onResponse (first.onOp operation) value)

/-- Functorial action of the free-extension construction on base and free
signatures and on result values. -/
def mapSignature (baseMap : SignatureMorphism base₁ base₂)
    (freeMap : SignatureMorphism free₁ free₂) (valueMap : α → β) :
    FreeExtension base₁ free₁ α → FreeExtension base₂ free₂ β
  | .ret value => .ret (valueMap value)
  | .baseOp operation continuation =>
      .baseOp (baseMap.onOp operation) (fun response =>
        mapSignature baseMap freeMap valueMap
          (continuation (baseMap.onResponse operation response)))
  | .freeOp operation continuation =>
      .freeOp (freeMap.onOp operation) (fun response =>
        mapSignature baseMap freeMap valueMap
          (continuation (freeMap.onResponse operation response)))

theorem mapSignature_bind
    (baseMap : SignatureMorphism base₁ base₂)
    (freeMap : SignatureMorphism free₁ free₂)
    (tree : FreeExtension base₁ free₁ α)
    (next : α → FreeExtension base₁ free₁ β) :
    mapSignature baseMap freeMap valueMap (tree.bind next) =
      (mapSignature baseMap freeMap id tree).bind
        (fun value => mapSignature baseMap freeMap valueMap (next value)) := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih =>
      simp only [bind, mapSignature]
      congr
      funext response
      exact ih (baseMap.onResponse operation response)
  | freeOp operation continuation ih =>
      simp only [bind, mapSignature]
      congr
      funext response
      exact ih (freeMap.onResponse operation response)

theorem mapSignature_id (tree : FreeExtension base free α) :
    mapSignature (SignatureMorphism.id base) (SignatureMorphism.id free) id tree = tree := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih =>
      simp only [mapSignature, SignatureMorphism.id]
      congr
      funext response
      exact ih response
  | freeOp operation continuation ih =>
      simp only [mapSignature, SignatureMorphism.id]
      congr
      funext response
      exact ih response

theorem mapSignature_comp
    (baseFirst : SignatureMorphism base₁ base₂)
    (baseSecond : SignatureMorphism base₂ base₃)
    (freeFirst : SignatureMorphism free₁ free₂)
    (freeSecond : SignatureMorphism free₂ free₃)
    (first : α → β) (second : β → γ)
    (tree : FreeExtension base₁ free₁ α) :
    mapSignature baseSecond freeSecond second
        (mapSignature baseFirst freeFirst first tree) =
      mapSignature (baseSecond.comp baseFirst) (freeSecond.comp freeFirst)
        (second ∘ first) tree := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih =>
      simp only [mapSignature, SignatureMorphism.comp]
      congr
      funext response
      exact ih (baseFirst.onResponse operation
        (baseSecond.onResponse (baseFirst.onOp operation) response))
  | freeOp operation continuation ih =>
      simp only [mapSignature, SignatureMorphism.comp]
      congr
      funext response
      exact ih (freeFirst.onResponse operation
        (freeSecond.onResponse (freeFirst.onOp operation) response))

/-- A heterogeneous relation between typed operation signatures. -/
structure SignatureRelation (left right : OperationSignature) where
  operation : left.Op → right.Op → Prop
  response : ∀ {leftOp rightOp}, operation leftOp rightOp →
    left.Response leftOp → right.Response rightOp → Prop

def SignatureRelation.identity (sig : OperationSignature) : SignatureRelation sig sig where
  operation := (· = ·)
  response := fun {leftOp rightOp} operations => by
    subst rightOp
    exact (· = ·)

def SignatureMorphism.graph (morphism : SignatureMorphism source target) :
    SignatureRelation source target where
  operation := fun sourceOp targetOp => morphism.onOp sourceOp = targetOp
  response := fun {sourceOp targetOp} operations => by
    subst targetOp
    exact fun sourceResponse targetResponse =>
      morphism.onResponse sourceOp targetResponse = sourceResponse

/-- Structural lifting of base-operation, free-operation and value relations. -/
inductive Rel (baseRel : SignatureRelation base₁ base₂)
    (freeRel : SignatureRelation free₁ free₂) (valueRel : α → β → Prop) :
    FreeExtension base₁ free₁ α → FreeExtension base₂ free₂ β → Prop where
  | ret : valueRel left right → Rel baseRel freeRel valueRel (.ret left) (.ret right)
  | baseOp (operations : baseRel.operation leftOp rightOp) :
      (∀ {leftResponse rightResponse},
        baseRel.response operations leftResponse rightResponse →
        Rel baseRel freeRel valueRel
          (leftContinuation leftResponse) (rightContinuation rightResponse)) →
      Rel baseRel freeRel valueRel
        (.baseOp leftOp leftContinuation) (.baseOp rightOp rightContinuation)
  | freeOp (operations : freeRel.operation leftOp rightOp) :
      (∀ {leftResponse rightResponse},
        freeRel.response operations leftResponse rightResponse →
        Rel baseRel freeRel valueRel
          (leftContinuation leftResponse) (rightContinuation rightResponse)) →
      Rel baseRel freeRel valueRel
        (.freeOp leftOp leftContinuation) (.freeOp rightOp rightContinuation)

theorem Rel.bind (treeRel : Rel baseRel freeRel valueRel left right)
    (nextRel : ∀ {leftValue rightValue}, valueRel leftValue rightValue →
      Rel baseRel freeRel resultRel (leftNext leftValue) (rightNext rightValue)) :
    Rel baseRel freeRel resultRel (left.bind leftNext) (right.bind rightNext) := by
  induction treeRel with
  | ret related => exact nextRel related
  | baseOp operations continuations ih => exact .baseOp operations (fun related => ih related)
  | freeOp operations continuations ih => exact .freeOp operations (fun related => ih related)

theorem Rel.reflEq (tree : FreeExtension base free α) :
    Rel (SignatureRelation.identity base) (SignatureRelation.identity free)
      (· = ·) tree tree := by
  induction tree with
  | ret value => exact .ret rfl
  | baseOp operation continuation ih =>
      apply Rel.baseOp rfl
      intro leftResponse rightResponse related
      subst rightResponse
      exact ih leftResponse
  | freeOp operation continuation ih =>
      apply Rel.freeOp rfl
      intro leftResponse rightResponse related
      subst rightResponse
      exact ih leftResponse

theorem Rel.graphMapSignature
    (baseMap : SignatureMorphism base₁ base₂)
    (freeMap : SignatureMorphism free₁ free₂)
    (valueMap : α → β) (tree : FreeExtension base₁ free₁ α) :
    Rel baseMap.graph freeMap.graph
      (fun left right => valueMap left = right) tree
      (mapSignature baseMap freeMap valueMap tree) := by
  induction tree with
  | ret value => exact .ret rfl
  | baseOp operation continuation ih =>
      apply Rel.baseOp rfl
      intro leftResponse rightResponse related
      subst leftResponse
      exact ih (baseMap.onResponse operation rightResponse)
  | freeOp operation continuation ih =>
      apply Rel.freeOp rfl
      intro leftResponse rightResponse related
      subst leftResponse
      exact ih (freeMap.onResponse operation rightResponse)

/-- An affine shallow handler.  Operations whose clause is absent are
forwarded; the first operation with a clause is replaced by the clause tree,
which is bound to the bare continuation. -/
structure AffineHandler (base free : OperationSignature) where
  clause : ∀ operation : free.Op,
    Option (FreeExtension base free (free.Response operation))

def shallow (handler : AffineHandler base free) :
    FreeExtension base free α → FreeExtension base free α
  | .ret value => .ret value
  | .baseOp operation continuation =>
      .baseOp operation (fun response => shallow handler (continuation response))
  | .freeOp operation continuation =>
      match handler.clause operation with
      | some responseTree => responseTree.bind continuation
      | none => .freeOp operation (fun response =>
          shallow handler (continuation response))

@[simp] theorem shallow_ret (handler : AffineHandler base free) (value : α) :
    shallow handler (.ret value) = .ret value := rfl

@[simp] theorem shallow_base (handler : AffineHandler base free)
    (operation : base.Op)
    (continuation : base.Response operation → FreeExtension base free α) :
    shallow handler (.baseOp operation continuation) =
      .baseOp operation (fun response => shallow handler (continuation response)) := rfl

theorem shallow_match (handler : AffineHandler base free)
    (found : handler.clause operation = some responseTree) :
    shallow handler (.freeOp operation continuation) =
      responseTree.bind continuation := by
  simp [shallow, found]

theorem shallow_forward (handler : AffineHandler base free)
    (missing : handler.clause operation = none) :
    shallow handler (.freeOp operation continuation) =
      .freeOp operation (fun response => shallow handler (continuation response)) := by
  simp [shallow, missing]

theorem shallow_map (handler : AffineHandler base free)
    (function : α → β) (tree : FreeExtension base free α) :
    map function (shallow handler tree) = shallow handler (map function tree) := by
  induction tree with
  | ret => rfl
  | baseOp operation continuation ih =>
      simp only [shallow, map, base_bind]
      congr
      funext response
      exact ih response
  | freeOp operation continuation ih =>
      cases found : handler.clause operation with
      | none =>
          rw [shallow_forward handler found]
          simp only [map, free_bind]
          rw [shallow_forward handler found]
          congr
          funext response
          exact ih response
      | some responseTree =>
          rw [shallow_match handler found]
          simp only [map, bind_assoc, free_bind]
          rw [shallow_match handler found]

theorem Rel.shallow
    (treeRel : Rel (SignatureRelation.identity base)
      (SignatureRelation.identity free) valueRel left right)
    (handler : AffineHandler base free) :
    Rel (SignatureRelation.identity base) (SignatureRelation.identity free)
      valueRel (shallow handler left) (shallow handler right) := by
  induction treeRel with
  | ret related => exact .ret related
  | baseOp operations continuations ih =>
      subst operations
      exact Rel.baseOp rfl (fun related => ih related)
  | freeOp operations continuations ih =>
      subst operations
      rename_i operation leftContinuation rightContinuation
      cases found : handler.clause operation with
      | none =>
          rw [shallow_forward handler found, shallow_forward handler found]
          exact Rel.freeOp rfl (fun related => ih related)
      | some responseTree =>
          rw [shallow_match handler found, shallow_match handler found]
          apply Rel.bind (Rel.reflEq responseTree)
          intro leftResponse rightResponse related
          subst rightResponse
          exact continuations rfl

end FreeExtension
end EffectSemantics
