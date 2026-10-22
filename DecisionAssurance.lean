import Std

/-!
Finite decision-assurance reference model.
Copyright (c) 2026 AI Assurance, Inc. All rights reserved.

The general lemmas concern explicit policies, encodings and possible outputs.
They do not authenticate policy authors, establish real-world facts, or prove
that the Python/JavaScript parser implements every definition in this file.
-/
namespace DecisionAssurance

universe u v w

/-- Every represented input has a judgment allowed in ALL its source states. -/
def RepresentationOK {X : Type u} {Z : Type v} {A : Type w}
    (domain : X → Prop) (encode : X → Z) (policy : X → A → Prop) : Prop :=
  ∀ z, (∃ x, domain x ∧ encode x = z) →
    ∃ a, ∀ x, domain x → encode x = z → policy x a

/-- Outputs are nonempty and every possible output is allowed in every source state. -/
def SpecificationOK {X : Type u} {Z : Type v} {A : Type w}
    (domain : X → Prop) (encode : X → Z) (policy : X → A → Prop)
    (outputs : Z → A → Prop) : Prop :=
  ∀ z, (∃ x, domain x ∧ encode x = z) →
    (∃ a, outputs z a) ∧
    (∀ a, outputs z a → ∀ x, domain x → encode x = z → policy x a)

/-- A specification with nonempty sound outputs requires an adequate representation. -/
theorem specification_requires_representation
    {X : Type u} {Z : Type v} {A : Type w}
    (domain : X → Prop) (encode : X → Z) (policy : X → A → Prop)
    (outputs : Z → A → Prop)
    (h : SpecificationOK domain encode policy outputs) :
    RepresentationOK domain encode policy := by
  intro z hz
  obtain ⟨hne, hs⟩ := h z hz
  obtain ⟨a, ha⟩ := hne
  exact ⟨a, fun x hx he => hs a ha x hx he⟩

/-- No downstream rule change repairs an input class with no common allowed judgment. -/
theorem collision_cannot_be_repaired_by_rule_only
    {X : Type u} {Z : Type v} {A : Type w}
    (domain : X → Prop) (encode : X → Z) (policy : X → A → Prop)
    (z : Z) (hz : ∃ x, domain x ∧ encode x = z)
    (bad : ¬ ∃ a, ∀ x, domain x → encode x = z → policy x a) :
    ∀ outputs : Z → A → Prop, ¬ SpecificationOK domain encode policy outputs := by
  intro outputs hs
  exact bad (specification_requires_representation domain encode policy outputs hs z hz)

/-- Specification soundness is about all possible outputs, not a favorable sample. -/
theorem every_possible_output_is_allowed
    {X : Type u} {Z : Type v} {A : Type w}
    (domain : X → Prop) (encode : X → Z) (policy : X → A → Prop)
    (outputs : Z → A → Prop)
    (h : SpecificationOK domain encode policy outputs)
    (x : X) (hx : domain x) (a : A) (ha : outputs (encode x) a) :
    policy x a := by
  have hs := h (encode x) ⟨x, hx, rfl⟩
  exact hs.2 a ha x hx rfl

/-- Empty output cannot satisfy the nonempty-output requirement. -/
theorem empty_output_cannot_pass
    {X : Type u} {Z : Type v} {A : Type w}
    (domain : X → Prop) (encode : X → Z) (policy : X → A → Prop)
    (outputs : Z → A → Prop) (x : X) (hx : domain x)
    (empty : ∀ a, ¬ outputs (encode x) a) :
    ¬ SpecificationOK domain encode policy outputs := by
  intro hs
  obtain ⟨a, ha⟩ := (hs (encode x) ⟨x, hx, rfl⟩).1
  exact empty a ha

/-- A required action excludes HOLD whenever HOLD is outside the policy set. -/
theorem forbidden_hold_cannot_be_a_possible_output
    {X : Type u} {Z : Type v} {A : Type w}
    (domain : X → Prop) (encode : X → Z) (policy : X → A → Prop)
    (outputs : Z → A → Prop) (x : X) (hx : domain x) (hold : A)
    (notAllowed : ¬ policy x hold)
    (hs : SpecificationOK domain encode policy outputs) :
    ¬ outputs (encode x) hold := by
  intro ho
  exact notAllowed (every_possible_output_is_allowed domain encode policy outputs hs x hx hold ho)

/-- A view must preserve both directions of the displayed judgment relation. -/
def ExplanationOK {X : Type u} {A : Type v}
    (domain : X → Prop) (reference displayed : X → A → Prop) : Prop :=
  ∀ x, domain x → ∀ a, displayed x a ↔ reference x a

theorem displayed_claim_is_supported
    {X : Type u} {A : Type v} (domain : X → Prop)
    (reference displayed : X → A → Prop)
    (he : ExplanationOK domain reference displayed)
    (x : X) (hx : domain x) (a : A) (hd : displayed x a) : reference x a :=
  (he x hx a).mp hd

theorem required_display_is_not_omitted
    {X : Type u} {A : Type v} (domain : X → Prop)
    (reference displayed : X → A → Prop)
    (he : ExplanationOK domain reference displayed)
    (x : X) (hx : domain x) (a : A) (hr : reference x a) : displayed x a :=
  (he x hx a).mpr hr

/-- Model-stage statuses and authenticated boundary observations remain separate. -/
structure GateInput where
  modelOK : Bool
  sameBundle : Bool
  currentApproval : Bool
  inScope : Bool
  samePayload : Bool
  deriving DecidableEq, Repr

def canUse (g : GateInput) : Bool :=
  g.modelOK && g.sameBundle && g.currentApproval && g.inScope && g.samePayload

theorem use_requires_all_conditions (g : GateInput) :
    canUse g = true ↔ g.modelOK = true ∧ g.sameBundle = true ∧
      g.currentApproval = true ∧ g.inScope = true ∧ g.samePayload = true := by
  cases g with
  | mk m b a s p =>
    cases m <;> cases b <;> cases a <;> cases s <;> cases p <;> decide

theorem revoked_approval_blocks (g : GateInput) (h : g.currentApproval = false) :
    canUse g = false := by
  simp [canUse, h]

theorem changed_bundle_blocks_old_permit (g : GateInput) (h : g.sameBundle = false) :
    canUse g = false := by
  simp [canUse, h]

theorem changed_payload_blocks (g : GateInput) (h : g.samePayload = false) :
    canUse g = false := by
  simp [canUse, h]

/-- Compatibility is not approval, and approval is not compatibility. -/
def jointAdoption (compatible verified explained approved : Bool) : Bool :=
  compatible && verified && explained && approved

theorem compatibility_is_not_approval (v e : Bool) :
    jointAdoption true v e false = false := by
  cases v <;> cases e <;> decide

theorem approvals_do_not_resolve_conflicting_conditions (v e a : Bool) :
    jointAdoption false v e a = false := by
  cases v <;> cases e <;> cases a <;> decide

/-- Finite model for the 64-state civic scenario. -/
inductive Evidence where
  | T | F | U | B
  deriving DecidableEq, Repr
inductive Action where
  | advance | review | reject | hold
  deriving DecidableEq, Repr
structure Situation where
  q : Evidence
  e : Evidence
  r : Evidence
  deriving DecidableEq, Repr

def evidenceStates : List Evidence := [.T, .F, .U, .B]
def situations : List Situation := evidenceStates.flatMap fun q =>
  evidenceStates.flatMap fun e => evidenceStates.map fun r => ⟨q, e, r⟩
def actions : List Action := [.advance, .review, .reject, .hold]

def policy (x : Situation) : Action :=
  if x.q == .B || x.e == .B || x.r == .B then .review
  else if x.r != .T then .hold
  else if x.q == .F then .reject
  else if x.q != .T || x.e != .T then .review
  else .advance

def collapseUnconfirmed (x : Situation) : Situation :=
  { x with e := if x.e == .U then .T else x.e }

def badRule (x : Situation) : Action :=
  if (x.q == .T || x.q == .U) && (x.e == .T || x.e == .U) && x.r == .T
  then .advance else policy x

def safety (x : Situation) (a : Action) : Bool :=
  if a == .advance then x.q == .T && x.e == .T && x.r == .T else true

def finiteRepresentation (encode : Situation → Situation) : Bool :=
  situations.all fun x => actions.any fun a =>
    situations.all fun y => if encode x == encode y then a == policy y else true

def finiteSpecification (encode : Situation → Situation) (f : Situation → Action) : Bool :=
  situations.all fun x => f (encode x) == policy x

def finiteSafety (f : Situation → Action) : Bool :=
  situations.all fun x => safety x (f x)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem exactly_64_situations : situations.length = 64 := by decide

theorem normal_representation_passes : finiteRepresentation id = true := by decide

theorem normal_specification_passes : finiteSpecification id policy = true := by decide

theorem normal_safety_passes : finiteSafety policy = true := by decide

theorem collapsed_representation_fails :
    finiteRepresentation collapseUnconfirmed = false := by decide

theorem bad_rule_fails_specification : finiteSpecification id badRule = false := by decide

theorem all_hold_satisfies_only_safety : finiteSafety (fun _ => .hold) = true := by decide

theorem all_hold_violates_mandatory_judgments :
    finiteSpecification id (fun _ => .hold) = false := by decide

/-- The implication permits HOLD; the actual specification emits ADVANCE. -/
theorem theorem_compatible_does_not_mean_actual_output :
    safety ⟨.T, .T, .T⟩ .hold = true ∧ policy ⟨.T, .T, .T⟩ ≠ .hold := by decide

/-- Generic finite table, projected from actual model inputs, not pass/fail flags. -/
structure Row where
  input : Nat
  allowed : List Nat
  outputs : List Nat
  premise : Bool
  theoremAllowed : List Nat
  deriving DecidableEq, Repr

def sameSet (xs ys : List Nat) : Bool :=
  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)

def commonActions (rows : List Row) (actionUniverse : List Nat) (input : Nat) : List Nat :=
  actionUniverse.filter fun a => rows.all fun r =>
    if r.input == input then r.allowed.contains a else true

def conditionCheck (rows : List Row) : Bool :=
  !rows.isEmpty && rows.all (fun r => !r.allowed.isEmpty)

def representationCheck (rows : List Row) (actionUniverse : List Nat) (full : Bool) : Bool :=
  !rows.isEmpty && rows.all fun r =>
    !(commonActions rows actionUniverse r.input).isEmpty &&
    (if full then rows.all (fun s => if r.input == s.input then sameSet r.allowed s.allowed else true)
     else true)

def specificationCheck (rows : List Row) (actionUniverse : List Nat) (full : Bool) : Bool :=
  !rows.isEmpty && rows.all fun r =>
    let common := commonActions rows actionUniverse r.input
    !r.outputs.isEmpty && r.outputs.all (fun a => common.contains a) &&
      (if full then sameSet r.outputs common else true)

def propositionCheck (rows : List Row) : Bool :=
  rows.any (fun r => r.premise) && rows.all (fun r =>
    if r.premise then !r.outputs.isEmpty && r.outputs.all (fun a => r.theoremAllowed.contains a)
    else true)

/-- Pairwise overlap is insufficient: all three source states are checked. -/
def tripleRows : List Row :=
  [⟨0, [0,1], [0], true, [0,1,2]⟩,
   ⟨0, [1,2], [0], true, [0,1,2]⟩,
   ⟨0, [0,2], [0], true, [0,1,2]⟩]

theorem triple_intersection_not_pairwise :
    conditionCheck tripleRows = true ∧
    representationCheck tripleRows [0,1,2] false = false := by decide

#print axioms specification_requires_representation
#print axioms collision_cannot_be_repaired_by_rule_only
#print axioms every_possible_output_is_allowed
#print axioms empty_output_cannot_pass
#print axioms forbidden_hold_cannot_be_a_possible_output
#print axioms displayed_claim_is_supported
#print axioms use_requires_all_conditions
#print axioms collapsed_representation_fails
#print axioms theorem_compatible_does_not_mean_actual_output
#print axioms triple_intersection_not_pairwise
end DecisionAssurance

-- BEGIN FINITE MODELS
namespace FiniteConformance
open DecisionAssurance
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def normal : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [3], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [3], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem normal_conditions : conditionCheck normal = true := by decide
theorem normal_representation : representationCheck normal [0, 1, 2, 3] false = true := by decide
theorem normal_specification : specificationCheck normal [0, 1, 2, 3] false = true := by decide
theorem normal_proposition : propositionCheck normal = true := by decide

def input_collision : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨42, [3], [0], true, [1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem input_collision_conditions : conditionCheck input_collision = true := by decide
theorem input_collision_representation : representationCheck input_collision [0, 1, 2, 3] false = false := by decide
theorem input_collision_specification : specificationCheck input_collision [0, 1, 2, 3] false = false := by decide
theorem input_collision_proposition : propositionCheck input_collision = false := by decide

def wrong_rule : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [0], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [0], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [0], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem wrong_rule_conditions : conditionCheck wrong_rule = true := by decide
theorem wrong_rule_representation : representationCheck wrong_rule [0, 1, 2, 3] false = true := by decide
theorem wrong_rule_specification : specificationCheck wrong_rule [0, 1, 2, 3] false = false := by decide
theorem wrong_rule_proposition : propositionCheck wrong_rule = false := by decide

def all_hold : List Row := [
  ⟨42, [0], [1], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [1], true, [1, 2, 3]⟩,
  ⟨38, [2], [1], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [1], true, [1, 2, 3]⟩,
  ⟨46, [3], [1], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [1], true, [1, 2, 3]⟩,
  ⟨34, [3], [1], true, [1, 2, 3]⟩,
  ⟨33, [3], [1], true, [1, 2, 3]⟩,
  ⟨35, [3], [1], true, [1, 2, 3]⟩,
  ⟨32, [3], [1], true, [1, 2, 3]⟩,
  ⟨26, [3], [1], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [1], true, [1, 2, 3]⟩,
  ⟨22, [2], [1], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [1], true, [1, 2, 3]⟩,
  ⟨30, [3], [1], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [1], true, [1, 2, 3]⟩,
  ⟨18, [3], [1], true, [1, 2, 3]⟩,
  ⟨17, [3], [1], true, [1, 2, 3]⟩,
  ⟨19, [3], [1], true, [1, 2, 3]⟩,
  ⟨16, [3], [1], true, [1, 2, 3]⟩,
  ⟨58, [3], [1], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [1], true, [1, 2, 3]⟩,
  ⟨54, [2], [1], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [1], true, [1, 2, 3]⟩,
  ⟨62, [3], [1], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [1], true, [1, 2, 3]⟩,
  ⟨50, [3], [1], true, [1, 2, 3]⟩,
  ⟨49, [3], [1], true, [1, 2, 3]⟩,
  ⟨51, [3], [1], true, [1, 2, 3]⟩,
  ⟨48, [3], [1], true, [1, 2, 3]⟩,
  ⟨10, [3], [1], true, [1, 2, 3]⟩,
  ⟨9, [3], [1], true, [1, 2, 3]⟩,
  ⟨11, [3], [1], true, [1, 2, 3]⟩,
  ⟨8, [3], [1], true, [1, 2, 3]⟩,
  ⟨6, [3], [1], true, [1, 2, 3]⟩,
  ⟨5, [3], [1], true, [1, 2, 3]⟩,
  ⟨7, [3], [1], true, [1, 2, 3]⟩,
  ⟨4, [3], [1], true, [1, 2, 3]⟩,
  ⟨14, [3], [1], true, [1, 2, 3]⟩,
  ⟨13, [3], [1], true, [1, 2, 3]⟩,
  ⟨15, [3], [1], true, [1, 2, 3]⟩,
  ⟨12, [3], [1], true, [1, 2, 3]⟩,
  ⟨2, [3], [1], true, [1, 2, 3]⟩,
  ⟨1, [3], [1], true, [1, 2, 3]⟩,
  ⟨3, [3], [1], true, [1, 2, 3]⟩,
  ⟨0, [3], [1], true, [1, 2, 3]⟩]
theorem all_hold_conditions : conditionCheck all_hold = true := by decide
theorem all_hold_representation : representationCheck all_hold [0, 1, 2, 3] false = true := by decide
theorem all_hold_specification : specificationCheck all_hold [0, 1, 2, 3] false = false := by decide
theorem all_hold_proposition : propositionCheck all_hold = true := by decide

def overclaim : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [3], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [3], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem overclaim_conditions : conditionCheck overclaim = true := by decide
theorem overclaim_representation : representationCheck overclaim [0, 1, 2, 3] false = true := by decide
theorem overclaim_specification : specificationCheck overclaim [0, 1, 2, 3] false = true := by decide
theorem overclaim_proposition : propositionCheck overclaim = true := by decide

def unparsed_text : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [3], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [3], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem unparsed_text_conditions : conditionCheck unparsed_text = true := by decide
theorem unparsed_text_representation : representationCheck unparsed_text [0, 1, 2, 3] false = true := by decide
theorem unparsed_text_specification : specificationCheck unparsed_text [0, 1, 2, 3] false = true := by decide
theorem unparsed_text_proposition : propositionCheck unparsed_text = true := by decide

def condition_conflict : List Row := [
  ⟨42, [], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [3], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [3], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem condition_conflict_conditions : conditionCheck condition_conflict = false := by decide
theorem condition_conflict_representation : representationCheck condition_conflict [0, 1, 2, 3] false = false := by decide
theorem condition_conflict_specification : specificationCheck condition_conflict [0, 1, 2, 3] false = false := by decide
theorem condition_conflict_proposition : propositionCheck condition_conflict = true := by decide

def wrong_approval : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [3], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [3], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem wrong_approval_conditions : conditionCheck wrong_approval = true := by decide
theorem wrong_approval_representation : representationCheck wrong_approval [0, 1, 2, 3] false = true := by decide
theorem wrong_approval_specification : specificationCheck wrong_approval [0, 1, 2, 3] false = true := by decide
theorem wrong_approval_proposition : propositionCheck wrong_approval = true := by decide

def revoked : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [3], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [3], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem revoked_conditions : conditionCheck revoked = true := by decide
theorem revoked_representation : representationCheck revoked [0, 1, 2, 3] false = true := by decide
theorem revoked_specification : specificationCheck revoked [0, 1, 2, 3] false = true := by decide
theorem revoked_proposition : propositionCheck revoked = true := by decide

def changed_version : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [3], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [3], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem changed_version_conditions : conditionCheck changed_version = true := by decide
theorem changed_version_representation : representationCheck changed_version [0, 1, 2, 3] false = true := by decide
theorem changed_version_specification : specificationCheck changed_version [0, 1, 2, 3] false = true := by decide
theorem changed_version_proposition : propositionCheck changed_version = true := by decide

def missing_approval : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [3], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [3], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem missing_approval_conditions : conditionCheck missing_approval = true := by decide
theorem missing_approval_representation : representationCheck missing_approval [0, 1, 2, 3] false = true := by decide
theorem missing_approval_specification : specificationCheck missing_approval [0, 1, 2, 3] false = true := by decide
theorem missing_approval_proposition : propositionCheck missing_approval = true := by decide

def duplicate_approval : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [3], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [3], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem duplicate_approval_conditions : conditionCheck duplicate_approval = true := by decide
theorem duplicate_approval_representation : representationCheck duplicate_approval [0, 1, 2, 3] false = true := by decide
theorem duplicate_approval_specification : specificationCheck duplicate_approval [0, 1, 2, 3] false = true := by decide
theorem duplicate_approval_proposition : propositionCheck duplicate_approval = true := by decide

def empty_output : List Row := [
  ⟨42, [0], [], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [], true, [1, 2, 3]⟩,
  ⟨43, [1], [], true, [1, 2, 3]⟩,
  ⟨40, [3], [], true, [1, 2, 3]⟩,
  ⟨38, [2], [], true, [1, 2, 3]⟩,
  ⟨37, [1], [], true, [1, 2, 3]⟩,
  ⟨39, [1], [], true, [1, 2, 3]⟩,
  ⟨36, [3], [], true, [1, 2, 3]⟩,
  ⟨46, [3], [], true, [1, 2, 3]⟩,
  ⟨45, [1], [], true, [1, 2, 3]⟩,
  ⟨47, [1], [], true, [1, 2, 3]⟩,
  ⟨44, [3], [], true, [1, 2, 3]⟩,
  ⟨34, [3], [], true, [1, 2, 3]⟩,
  ⟨33, [3], [], true, [1, 2, 3]⟩,
  ⟨35, [3], [], true, [1, 2, 3]⟩,
  ⟨32, [3], [], true, [1, 2, 3]⟩,
  ⟨26, [3], [], true, [1, 2, 3]⟩,
  ⟨25, [1], [], true, [1, 2, 3]⟩,
  ⟨27, [1], [], true, [1, 2, 3]⟩,
  ⟨24, [3], [], true, [1, 2, 3]⟩,
  ⟨22, [2], [], true, [1, 2, 3]⟩,
  ⟨21, [1], [], true, [1, 2, 3]⟩,
  ⟨23, [1], [], true, [1, 2, 3]⟩,
  ⟨20, [3], [], true, [1, 2, 3]⟩,
  ⟨30, [3], [], true, [1, 2, 3]⟩,
  ⟨29, [1], [], true, [1, 2, 3]⟩,
  ⟨31, [1], [], true, [1, 2, 3]⟩,
  ⟨28, [3], [], true, [1, 2, 3]⟩,
  ⟨18, [3], [], true, [1, 2, 3]⟩,
  ⟨17, [3], [], true, [1, 2, 3]⟩,
  ⟨19, [3], [], true, [1, 2, 3]⟩,
  ⟨16, [3], [], true, [1, 2, 3]⟩,
  ⟨58, [3], [], true, [1, 2, 3]⟩,
  ⟨57, [1], [], true, [1, 2, 3]⟩,
  ⟨59, [1], [], true, [1, 2, 3]⟩,
  ⟨56, [3], [], true, [1, 2, 3]⟩,
  ⟨54, [2], [], true, [1, 2, 3]⟩,
  ⟨53, [1], [], true, [1, 2, 3]⟩,
  ⟨55, [1], [], true, [1, 2, 3]⟩,
  ⟨52, [3], [], true, [1, 2, 3]⟩,
  ⟨62, [3], [], true, [1, 2, 3]⟩,
  ⟨61, [1], [], true, [1, 2, 3]⟩,
  ⟨63, [1], [], true, [1, 2, 3]⟩,
  ⟨60, [3], [], true, [1, 2, 3]⟩,
  ⟨50, [3], [], true, [1, 2, 3]⟩,
  ⟨49, [3], [], true, [1, 2, 3]⟩,
  ⟨51, [3], [], true, [1, 2, 3]⟩,
  ⟨48, [3], [], true, [1, 2, 3]⟩,
  ⟨10, [3], [], true, [1, 2, 3]⟩,
  ⟨9, [3], [], true, [1, 2, 3]⟩,
  ⟨11, [3], [], true, [1, 2, 3]⟩,
  ⟨8, [3], [], true, [1, 2, 3]⟩,
  ⟨6, [3], [], true, [1, 2, 3]⟩,
  ⟨5, [3], [], true, [1, 2, 3]⟩,
  ⟨7, [3], [], true, [1, 2, 3]⟩,
  ⟨4, [3], [], true, [1, 2, 3]⟩,
  ⟨14, [3], [], true, [1, 2, 3]⟩,
  ⟨13, [3], [], true, [1, 2, 3]⟩,
  ⟨15, [3], [], true, [1, 2, 3]⟩,
  ⟨12, [3], [], true, [1, 2, 3]⟩,
  ⟨2, [3], [], true, [1, 2, 3]⟩,
  ⟨1, [3], [], true, [1, 2, 3]⟩,
  ⟨3, [3], [], true, [1, 2, 3]⟩,
  ⟨0, [3], [], true, [1, 2, 3]⟩]
theorem empty_output_conditions : conditionCheck empty_output = true := by decide
theorem empty_output_representation : representationCheck empty_output [0, 1, 2, 3] false = true := by decide
theorem empty_output_specification : specificationCheck empty_output [0, 1, 2, 3] false = false := by decide
theorem empty_output_proposition : propositionCheck empty_output = false := by decide

def vacuous_scope : List Row := [
  ⟨42, [0], [0], false, []⟩,
  ⟨41, [1], [1], false, []⟩,
  ⟨43, [1], [1], false, []⟩,
  ⟨40, [3], [3], false, []⟩,
  ⟨38, [2], [2], false, []⟩,
  ⟨37, [1], [1], false, []⟩,
  ⟨39, [1], [1], false, []⟩,
  ⟨36, [3], [3], false, []⟩,
  ⟨46, [3], [3], false, []⟩,
  ⟨45, [1], [1], false, []⟩,
  ⟨47, [1], [1], false, []⟩,
  ⟨44, [3], [3], false, []⟩,
  ⟨34, [3], [3], false, []⟩,
  ⟨33, [3], [3], false, []⟩,
  ⟨35, [3], [3], false, []⟩,
  ⟨32, [3], [3], false, []⟩,
  ⟨26, [3], [3], false, []⟩,
  ⟨25, [1], [1], false, []⟩,
  ⟨27, [1], [1], false, []⟩,
  ⟨24, [3], [3], false, []⟩,
  ⟨22, [2], [2], false, []⟩,
  ⟨21, [1], [1], false, []⟩,
  ⟨23, [1], [1], false, []⟩,
  ⟨20, [3], [3], false, []⟩,
  ⟨30, [3], [3], false, []⟩,
  ⟨29, [1], [1], false, []⟩,
  ⟨31, [1], [1], false, []⟩,
  ⟨28, [3], [3], false, []⟩,
  ⟨18, [3], [3], false, []⟩,
  ⟨17, [3], [3], false, []⟩,
  ⟨19, [3], [3], false, []⟩,
  ⟨16, [3], [3], false, []⟩,
  ⟨58, [3], [3], false, []⟩,
  ⟨57, [1], [1], false, []⟩,
  ⟨59, [1], [1], false, []⟩,
  ⟨56, [3], [3], false, []⟩,
  ⟨54, [2], [2], false, []⟩,
  ⟨53, [1], [1], false, []⟩,
  ⟨55, [1], [1], false, []⟩,
  ⟨52, [3], [3], false, []⟩,
  ⟨62, [3], [3], false, []⟩,
  ⟨61, [1], [1], false, []⟩,
  ⟨63, [1], [1], false, []⟩,
  ⟨60, [3], [3], false, []⟩,
  ⟨50, [3], [3], false, []⟩,
  ⟨49, [3], [3], false, []⟩,
  ⟨51, [3], [3], false, []⟩,
  ⟨48, [3], [3], false, []⟩,
  ⟨10, [3], [3], false, []⟩,
  ⟨9, [3], [3], false, []⟩,
  ⟨11, [3], [3], false, []⟩,
  ⟨8, [3], [3], false, []⟩,
  ⟨6, [3], [3], false, []⟩,
  ⟨5, [3], [3], false, []⟩,
  ⟨7, [3], [3], false, []⟩,
  ⟨4, [3], [3], false, []⟩,
  ⟨14, [3], [3], false, []⟩,
  ⟨13, [3], [3], false, []⟩,
  ⟨15, [3], [3], false, []⟩,
  ⟨12, [3], [3], false, []⟩,
  ⟨2, [3], [3], false, []⟩,
  ⟨1, [3], [3], false, []⟩,
  ⟨3, [3], [3], false, []⟩,
  ⟨0, [3], [3], false, []⟩]
theorem vacuous_scope_conditions : conditionCheck vacuous_scope = true := by decide
theorem vacuous_scope_representation : representationCheck vacuous_scope [0, 1, 2, 3] false = true := by decide
theorem vacuous_scope_specification : specificationCheck vacuous_scope [0, 1, 2, 3] false = true := by decide
theorem vacuous_scope_proposition : propositionCheck vacuous_scope = false := by decide

def missing_view_row : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [3], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [3], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem missing_view_row_conditions : conditionCheck missing_view_row = true := by decide
theorem missing_view_row_representation : representationCheck missing_view_row [0, 1, 2, 3] false = true := by decide
theorem missing_view_row_specification : specificationCheck missing_view_row [0, 1, 2, 3] false = true := by decide
theorem missing_view_row_proposition : propositionCheck missing_view_row = true := by decide

def invalid_authority : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [3], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [3], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem invalid_authority_conditions : conditionCheck invalid_authority = true := by decide
theorem invalid_authority_representation : representationCheck invalid_authority [0, 1, 2, 3] false = true := by decide
theorem invalid_authority_specification : specificationCheck invalid_authority [0, 1, 2, 3] false = true := by decide
theorem invalid_authority_proposition : propositionCheck invalid_authority = true := by decide

def wrong_role : List Row := [
  ⟨42, [0], [0], true, [0, 1, 2, 3]⟩,
  ⟨41, [1], [1], true, [1, 2, 3]⟩,
  ⟨43, [1], [1], true, [1, 2, 3]⟩,
  ⟨40, [3], [3], true, [1, 2, 3]⟩,
  ⟨38, [2], [2], true, [1, 2, 3]⟩,
  ⟨37, [1], [1], true, [1, 2, 3]⟩,
  ⟨39, [1], [1], true, [1, 2, 3]⟩,
  ⟨36, [3], [3], true, [1, 2, 3]⟩,
  ⟨46, [3], [3], true, [1, 2, 3]⟩,
  ⟨45, [1], [1], true, [1, 2, 3]⟩,
  ⟨47, [1], [1], true, [1, 2, 3]⟩,
  ⟨44, [3], [3], true, [1, 2, 3]⟩,
  ⟨34, [3], [3], true, [1, 2, 3]⟩,
  ⟨33, [3], [3], true, [1, 2, 3]⟩,
  ⟨35, [3], [3], true, [1, 2, 3]⟩,
  ⟨32, [3], [3], true, [1, 2, 3]⟩,
  ⟨26, [3], [3], true, [1, 2, 3]⟩,
  ⟨25, [1], [1], true, [1, 2, 3]⟩,
  ⟨27, [1], [1], true, [1, 2, 3]⟩,
  ⟨24, [3], [3], true, [1, 2, 3]⟩,
  ⟨22, [2], [2], true, [1, 2, 3]⟩,
  ⟨21, [1], [1], true, [1, 2, 3]⟩,
  ⟨23, [1], [1], true, [1, 2, 3]⟩,
  ⟨20, [3], [3], true, [1, 2, 3]⟩,
  ⟨30, [3], [3], true, [1, 2, 3]⟩,
  ⟨29, [1], [1], true, [1, 2, 3]⟩,
  ⟨31, [1], [1], true, [1, 2, 3]⟩,
  ⟨28, [3], [3], true, [1, 2, 3]⟩,
  ⟨18, [3], [3], true, [1, 2, 3]⟩,
  ⟨17, [3], [3], true, [1, 2, 3]⟩,
  ⟨19, [3], [3], true, [1, 2, 3]⟩,
  ⟨16, [3], [3], true, [1, 2, 3]⟩,
  ⟨58, [3], [3], true, [1, 2, 3]⟩,
  ⟨57, [1], [1], true, [1, 2, 3]⟩,
  ⟨59, [1], [1], true, [1, 2, 3]⟩,
  ⟨56, [3], [3], true, [1, 2, 3]⟩,
  ⟨54, [2], [2], true, [1, 2, 3]⟩,
  ⟨53, [1], [1], true, [1, 2, 3]⟩,
  ⟨55, [1], [1], true, [1, 2, 3]⟩,
  ⟨52, [3], [3], true, [1, 2, 3]⟩,
  ⟨62, [3], [3], true, [1, 2, 3]⟩,
  ⟨61, [1], [1], true, [1, 2, 3]⟩,
  ⟨63, [1], [1], true, [1, 2, 3]⟩,
  ⟨60, [3], [3], true, [1, 2, 3]⟩,
  ⟨50, [3], [3], true, [1, 2, 3]⟩,
  ⟨49, [3], [3], true, [1, 2, 3]⟩,
  ⟨51, [3], [3], true, [1, 2, 3]⟩,
  ⟨48, [3], [3], true, [1, 2, 3]⟩,
  ⟨10, [3], [3], true, [1, 2, 3]⟩,
  ⟨9, [3], [3], true, [1, 2, 3]⟩,
  ⟨11, [3], [3], true, [1, 2, 3]⟩,
  ⟨8, [3], [3], true, [1, 2, 3]⟩,
  ⟨6, [3], [3], true, [1, 2, 3]⟩,
  ⟨5, [3], [3], true, [1, 2, 3]⟩,
  ⟨7, [3], [3], true, [1, 2, 3]⟩,
  ⟨4, [3], [3], true, [1, 2, 3]⟩,
  ⟨14, [3], [3], true, [1, 2, 3]⟩,
  ⟨13, [3], [3], true, [1, 2, 3]⟩,
  ⟨15, [3], [3], true, [1, 2, 3]⟩,
  ⟨12, [3], [3], true, [1, 2, 3]⟩,
  ⟨2, [3], [3], true, [1, 2, 3]⟩,
  ⟨1, [3], [3], true, [1, 2, 3]⟩,
  ⟨3, [3], [3], true, [1, 2, 3]⟩,
  ⟨0, [3], [3], true, [1, 2, 3]⟩]
theorem wrong_role_conditions : conditionCheck wrong_role = true := by decide
theorem wrong_role_representation : representationCheck wrong_role [0, 1, 2, 3] false = true := by decide
theorem wrong_role_specification : specificationCheck wrong_role [0, 1, 2, 3] false = true := by decide
theorem wrong_role_proposition : propositionCheck wrong_role = true := by decide

def sharing_normal : List Row := [
  ⟨26, [3], [3], true, [0, 1, 3]⟩,
  ⟨27, [0], [0], true, [0, 1]⟩,
  ⟨24, [0], [0], true, [0, 1]⟩,
  ⟨25, [0], [0], true, [0, 1]⟩,
  ⟨22, [1], [1], true, [0, 1]⟩,
  ⟨23, [0], [0], true, [0, 1]⟩,
  ⟨20, [0], [0], true, [0, 1]⟩,
  ⟨21, [0], [0], true, [0, 1]⟩,
  ⟨30, [1], [1], true, [0, 1]⟩,
  ⟨31, [0], [0], true, [0, 1]⟩,
  ⟨28, [0], [0], true, [0, 1]⟩,
  ⟨29, [0], [0], true, [0, 1]⟩,
  ⟨18, [1], [1], true, [0, 1]⟩,
  ⟨19, [0], [0], true, [0, 1]⟩,
  ⟨16, [0], [0], true, [0, 1]⟩,
  ⟨17, [0], [0], true, [0, 1]⟩,
  ⟨10, [0], [0], true, [0, 1]⟩,
  ⟨11, [0], [0], true, [0, 1]⟩,
  ⟨8, [0], [0], true, [0, 1]⟩,
  ⟨9, [0], [0], true, [0, 1]⟩,
  ⟨6, [0], [0], true, [0, 1]⟩,
  ⟨7, [0], [0], true, [0, 1]⟩,
  ⟨4, [0], [0], true, [0, 1]⟩,
  ⟨5, [0], [0], true, [0, 1]⟩,
  ⟨14, [0], [0], true, [0, 1]⟩,
  ⟨15, [0], [0], true, [0, 1]⟩,
  ⟨12, [0], [0], true, [0, 1]⟩,
  ⟨13, [0], [0], true, [0, 1]⟩,
  ⟨2, [0], [0], true, [0, 1]⟩,
  ⟨3, [0], [0], true, [0, 1]⟩,
  ⟨0, [0], [0], true, [0, 1]⟩,
  ⟨1, [0], [0], true, [0, 1]⟩]
theorem sharing_normal_conditions : conditionCheck sharing_normal = true := by decide
theorem sharing_normal_representation : representationCheck sharing_normal [0, 1, 2, 3] false = true := by decide
theorem sharing_normal_specification : specificationCheck sharing_normal [0, 1, 2, 3] false = true := by decide
theorem sharing_normal_proposition : propositionCheck sharing_normal = true := by decide

def payload_mismatch : List Row := [
  ⟨26, [3], [2], true, [0, 1, 3]⟩,
  ⟨27, [0], [0], true, [0, 1]⟩,
  ⟨24, [0], [0], true, [0, 1]⟩,
  ⟨25, [0], [0], true, [0, 1]⟩,
  ⟨22, [1], [1], true, [0, 1]⟩,
  ⟨23, [0], [0], true, [0, 1]⟩,
  ⟨20, [0], [0], true, [0, 1]⟩,
  ⟨21, [0], [0], true, [0, 1]⟩,
  ⟨30, [1], [1], true, [0, 1]⟩,
  ⟨31, [0], [0], true, [0, 1]⟩,
  ⟨28, [0], [0], true, [0, 1]⟩,
  ⟨29, [0], [0], true, [0, 1]⟩,
  ⟨18, [1], [1], true, [0, 1]⟩,
  ⟨19, [0], [0], true, [0, 1]⟩,
  ⟨16, [0], [0], true, [0, 1]⟩,
  ⟨17, [0], [0], true, [0, 1]⟩,
  ⟨10, [0], [0], true, [0, 1]⟩,
  ⟨11, [0], [0], true, [0, 1]⟩,
  ⟨8, [0], [0], true, [0, 1]⟩,
  ⟨9, [0], [0], true, [0, 1]⟩,
  ⟨6, [0], [0], true, [0, 1]⟩,
  ⟨7, [0], [0], true, [0, 1]⟩,
  ⟨4, [0], [0], true, [0, 1]⟩,
  ⟨5, [0], [0], true, [0, 1]⟩,
  ⟨14, [0], [0], true, [0, 1]⟩,
  ⟨15, [0], [0], true, [0, 1]⟩,
  ⟨12, [0], [0], true, [0, 1]⟩,
  ⟨13, [0], [0], true, [0, 1]⟩,
  ⟨2, [0], [0], true, [0, 1]⟩,
  ⟨3, [0], [0], true, [0, 1]⟩,
  ⟨0, [0], [0], true, [0, 1]⟩,
  ⟨1, [0], [0], true, [0, 1]⟩]
theorem payload_mismatch_conditions : conditionCheck payload_mismatch = true := by decide
theorem payload_mismatch_representation : representationCheck payload_mismatch [0, 1, 2, 3] false = true := by decide
theorem payload_mismatch_specification : specificationCheck payload_mismatch [0, 1, 2, 3] false = false := by decide
theorem payload_mismatch_proposition : propositionCheck payload_mismatch = false := by decide

def purpose_collision : List Row := [
  ⟨12, [3], [3], true, [0, 1, 3]⟩,
  ⟨13, [0], [0], true, [0, 1]⟩,
  ⟨12, [0], [3], true, [0, 1]⟩,
  ⟨13, [0], [0], true, [0, 1]⟩,
  ⟨10, [1], [1], true, [0, 1]⟩,
  ⟨11, [0], [0], true, [0, 1]⟩,
  ⟨10, [0], [1], true, [0, 1]⟩,
  ⟨11, [0], [0], true, [0, 1]⟩,
  ⟨14, [1], [1], true, [0, 1]⟩,
  ⟨15, [0], [0], true, [0, 1]⟩,
  ⟨14, [0], [1], true, [0, 1]⟩,
  ⟨15, [0], [0], true, [0, 1]⟩,
  ⟨8, [1], [1], true, [0, 1]⟩,
  ⟨9, [0], [0], true, [0, 1]⟩,
  ⟨8, [0], [1], true, [0, 1]⟩,
  ⟨9, [0], [0], true, [0, 1]⟩,
  ⟨4, [0], [0], true, [0, 1]⟩,
  ⟨5, [0], [0], true, [0, 1]⟩,
  ⟨4, [0], [0], true, [0, 1]⟩,
  ⟨5, [0], [0], true, [0, 1]⟩,
  ⟨2, [0], [0], true, [0, 1]⟩,
  ⟨3, [0], [0], true, [0, 1]⟩,
  ⟨2, [0], [0], true, [0, 1]⟩,
  ⟨3, [0], [0], true, [0, 1]⟩,
  ⟨6, [0], [0], true, [0, 1]⟩,
  ⟨7, [0], [0], true, [0, 1]⟩,
  ⟨6, [0], [0], true, [0, 1]⟩,
  ⟨7, [0], [0], true, [0, 1]⟩,
  ⟨0, [0], [0], true, [0, 1]⟩,
  ⟨1, [0], [0], true, [0, 1]⟩,
  ⟨0, [0], [0], true, [0, 1]⟩,
  ⟨1, [0], [0], true, [0, 1]⟩]
theorem purpose_collision_conditions : conditionCheck purpose_collision = true := by decide
theorem purpose_collision_representation : representationCheck purpose_collision [0, 1, 2, 3] false = false := by decide
theorem purpose_collision_specification : specificationCheck purpose_collision [0, 1, 2, 3] false = false := by decide
theorem purpose_collision_proposition : propositionCheck purpose_collision = false := by decide

end FiniteConformance
-- END FINITE MODELS
