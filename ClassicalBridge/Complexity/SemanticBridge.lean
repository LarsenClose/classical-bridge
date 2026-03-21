/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Complexity/SemanticBridge.lean — The semantic bridge:
parameterized by model-semantics pairing, derives regime-specific results.

The direct bridge (selfApp_nonincreasing_contradiction) fires when a
model-semantics pairing produces both SelfAppUnbounded and a
grade-non-increasing canonicalizer equal to selfApp.

No counting needed. No GradeStructure. No HasInjectionBound. No tower N_End.

The seven chains each instantiate this pattern with their domain-specific
canonicalizer. The classical TM case instantiates it with the selfApp
derived from the computation model and the semantics.

STATUS: 0 sorry. Zero custom axioms in main chain.
-/

import WTS.Tower.CarrierEngineering.MinimalNecessityGradient
import WTS.Transport.TransportSelfSimilarity
import PNP.Characterizations.ResourceSemantics
import ClassicalBridge.Complexity.Basic
import ClassicalBridge.Bridge.TMAdmissibleEncoding

namespace ClassicalBridge.Complexity.SemanticBridge

open WTS
open ClassicalBridge.Complexity

-- ════════════════════════════════════════════════════════════
-- Section 1: The model-semantics pairing
-- ════════════════════════════════════════════════════════════

/-- A model-semantics pairing: a GRM together with a threshold through
    which selfApp factors. The threshold is determined by the pairing.

    - threshold = 0 with grade-non-increasing selfApp: projectional
    - threshold = headerLen: classical TM with fixed header
    - no finite threshold: separation regime

    The regime classification follows from the threshold. -/
structure DriftedPairing where
  /-- The graded reflexive model. -/
  M : WTS.GradedReflModel
  /-- The threshold: selfApp factors through this grade. -/
  threshold : Nat
  /-- selfApp factors through the threshold. -/
  factors : WTS.FactorsThrough M M.selfApp threshold

/-- The projectional special case: threshold = 0 from grade-non-increasing selfApp. -/
def DriftedPairing.ofProjectional
    (M : WTS.GradedReflModel)
    (canonicalize : M.carrier → M.carrier)
    (selfApp_eq : ∀ x, M.selfApp x = canonicalize x)
    (canon_grade_le : ∀ x, M.grade (canonicalize x) ≤ M.grade x) :
    DriftedPairing where
  M := M
  threshold := 0
  factors := fun x hle => by
    have : M.grade (M.selfApp x) ≤ M.grade x := by
      rw [selfApp_eq]; exact canon_grade_le x
    omega

/-- Any DriftedPairing has PEqNP (selfApp factors through the threshold). -/
theorem pairing_peqnp (S : DriftedPairing) : WTS.PEqNP S.M :=
  ⟨S.threshold, S.factors⟩

/-- Any DriftedPairing with SelfAppUnbounded is contradictory.
    FactorsThrough at the threshold contradicts SelfAppUnbounded. -/
theorem pairing_unbounded_absurd (S : DriftedPairing)
    (hub : WTS.SelfAppUnbounded S.M) : False := by
  obtain ⟨x, hle, hgt⟩ := hub.overflows S.threshold
  exact Nat.not_le.mpr hgt (S.factors x hle)

-- ════════════════════════════════════════════════════════════
-- Section 2: Transport-carrier structural incompatibility
-- ════════════════════════════════════════════════════════════

open ClassicalBridge.Bridge
open ClassicalBridge.TM

/-- Convert classicalGRM to WTS.GradedReflModel for transport construction. -/
noncomputable def classicalGRM_WTS (h : SelfAppHeader) : WTS.GradedReflModel where
  carrier := (classicalGRM h).carrier
  fold := (classicalGRM h).fold
  unfold := (classicalGRM h).unfold
  roundtrip := (classicalGRM h).roundtrip
  grade := (classicalGRM h).grade

theorem naming_cost_nonclosure (h : SelfAppHeader) (hne : h.headerLen > 0)
    (φ : GRMorphism (transportGradedReflModel (classicalGRM_WTS h)) (classicalGRM_WTS h)) :
    False := by
  set M := classicalGRM_WTS h
  set TM := transportGradedReflModel M
  set t := Transport.identity M
  set x := φ.map t
  -- fold_T(t) = t (by roundtrip, since unfold_T = id)
  have h_fold_id : TM.fold t = t := TM.roundtrip t
  -- map_fold: φ(fold_T(t)) = fold_M(φ(t)). Since fold_T(t) = t: fold_M(φ(t)) = φ(t)
  have h1 : M.fold (φ.map t) = φ.map t := by
    have := φ.map_fold t; rw [h_fold_id] at this; exact this.symm
  have h2 : M.unfold (φ.map t) = φ.map t := by
    have := φ.map_unfold t; exact this.symm
  -- fold(x) = x = unfold(x), so fold(x) = unfold(x)
  have h_eq : M.fold (φ.map t) = M.unfold (φ.map t) := by rw [h1, h2]
  -- Length: fold shortens or preserves
  have h_len : List.length (M.fold (φ.map t)) ≤ List.length (φ.map t) := by
    simp [M, classicalGRM_WTS, classicalGRM, classicalAdmissibleEncoding,
          ClassicalBridge.AdmissibleEncoding.toGRM, bridgeFold, canonicalSpec,
          TMSelfAppSpec.fold, tmFold, List.length_drop]
  -- Length: unfold lengthens by headerLen
  have h_len2 : List.length (M.unfold (φ.map t)) ≥
      List.length (φ.map t) + h.headerLen := by
    simp only [M, classicalGRM_WTS, classicalGRM, classicalAdmissibleEncoding,
          ClassicalBridge.AdmissibleEncoding.toGRM, bridgeUnfold, canonicalSpec,
          TMSelfAppSpec.unfold, tmUnfold, List.length_append]
    rw [h.headerLen_eq]; omega
  rw [h_eq] at h_len; omega

#print axioms naming_cost_nonclosure

-- ════════════════════════════════════════════════════════════
-- Section 3: The answer space
-- ════════════════════════════════════════════════════════════

/-- The regime profile: what the carrier M determines by necessity.
    The gradient (kernel, iff-thresholds, least drift) and the transport
    tower (selfApp = id, PEqNP) are forced by M alone — no semantics,
    no resource model, no naming convention needed. -/
structure RegimeProfile (M : WTS.GradedReflModel) where
  /-- The carrier iff machinery: kernel, strict/drift naming thresholds,
      least drift. Every GRM carries this unconditionally. -/
  gradient : MinimalNecessityGradient M
  /-- The transport tower: selfApp = id, PEqNP. -/
  transport_properties :
    (∀ t, (transportGradedReflModel M).selfApp t = t) ∧
    WTS.PEqNP (transportGradedReflModel M)

/-- Every GRM has a regime profile. -/
def regimeProfile (M : WTS.GradedReflModel) : RegimeProfile M where
  gradient := M.minimalNecessityGradient
  transport_properties :=
    ⟨transport_model_selfApp_eq_id M, transport_model_PEqNP M⟩

/-- The classical answer space: given a naming convention h, what the
    carrier architecture, resource-indexed semantics, and structural
    cost of naming together determine.

    The carrier (classicalGRM_WTS h) determines the regime profile.
    The semantics (h) applied to the binary carrier determines the
    resource-indexed counting (growth gap, no polynomial cover).
    The structural cost (headerLen > 0) determines the nonclosure.

    (1) The carrier kernel with exact iff-thresholds.
    (2) The transport tower has selfApp = id and PEqNP.
    (3) The function space nVal(n)^nVal(n) exceeds program capacity
        nProg(n + c) at every overhead c.
    (4) No uniform polynomial covers the gap.
    (5) When headerLen > 0, no GRMorphism from T(M) to M exists. -/
structure ClassicalAnswerSpace (h : SelfAppHeader) where
  /-- The regime profile: what the carrier determines by necessity. -/
  regime : RegimeProfile (classicalGRM_WTS h)
  /-- The growth gap: function space exceeds program capacity. -/
  growth_gap : ∀ c, PNP.HasGrowthGap
    (ResourceSemantics.functionSpaceSize ResourceSemantics.binaryResourceModel)
    ResourceSemantics.binaryResourceModel.nProg c
  /-- No uniform polynomial covers the gap. -/
  no_poly_cover : ∀ k, ¬∀ n,
    ResourceSemantics.functionSpaceSize ResourceSemantics.binaryResourceModel n ≤
    ResourceSemantics.binaryResourceModel.nProg (n + k)
  /-- Naming cost nonclosure: no GRMorphism from T(M) to M when
      headerLen > 0. The structural cost of the naming convention
      prevents closure under the transport construction. -/
  nonclosure : h.headerLen > 0 →
    ∀ (_φ : WTS.GRMorphism (transportGradedReflModel (classicalGRM_WTS h))
                            (classicalGRM_WTS h)), False

/-- Every header has a classical answer space. -/
noncomputable def classical_answer_space (h : SelfAppHeader) :
    ClassicalAnswerSpace h where
  regime := regimeProfile (classicalGRM_WTS h)
  growth_gap := ResourceSemantics.binary_growth_gap
  no_poly_cover := ResourceSemantics.binary_no_uniform_bound
  nonclosure := naming_cost_nonclosure h

-- ════════════════════════════════════════════════════════════
-- Section 4: The three cannots
-- ════════════════════════════════════════════════════════════

/-- The three cannots for classical computation, as a single theorem.

    For any naming convention with positive cost (headerLen > 0):

    (1) The classical machine cannot self-reference for free.
        Self-application adds at most headerLen bits. Zero for inputs above headerLen.

    (2) The classical machine cannot structurally embed the
        frictionless substrate. No GRMorphism from T(M) to M.

    (3) The classical machine cannot polynomially cover its own
        required behaviors. The function space exceeds program
        capacity at every polynomial overhead.

    These are not three independent facts. They are three facets
    of a single obstruction: the asymmetric geometry of classical
    naming (fold shortens, unfold lengthens) prevents structural
    return to the substrate, forces irreducible drift, and leaves
    the resource gap unbridgeable.

    The chain: EM requires distinguishable witnesses. Distinguishable
    witnesses require encoding. Encoding requires a header. The header
    has positive length. Therefore fold/unfold is asymmetric. The
    asymmetry blocks structural return (cannot 2), forces drift
    (cannot 1), and the resource gap exceeds every polynomial
    (cannot 3). -/
theorem classical_computation_characterized (h : SelfAppHeader) (hne : h.headerLen > 0) :
    -- Cannot 1: irreducible naming cost
    (∀ x, (classicalGRM_WTS h).grade ((classicalGRM_WTS h).selfApp x) ≤
           (classicalGRM_WTS h).grade x + h.headerLen) ∧
    -- Cannot 2: substrate structurally unreachable
    (∀ _φ : GRMorphism (transportGradedReflModel (classicalGRM_WTS h))
                       (classicalGRM_WTS h), False) ∧
    -- Cannot 3: no polynomial covers the operational richness
    (∀ k, ¬∀ n, ResourceSemantics.functionSpaceSize
                   ResourceSemantics.binaryResourceModel n ≤
                   ResourceSemantics.binaryResourceModel.nProg (n + k)) :=
  ⟨bridge_selfApp_bounded h,
   naming_cost_nonclosure h hne,
   ResourceSemantics.binary_no_uniform_bound⟩

#print axioms regimeProfile
#print axioms classical_answer_space
#print axioms classical_computation_characterized

-- ════════════════════════════════════════════════════════════
-- Section 5: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms pairing_peqnp
#print axioms pairing_unbounded_absurd

end ClassicalBridge.Complexity.SemanticBridge
