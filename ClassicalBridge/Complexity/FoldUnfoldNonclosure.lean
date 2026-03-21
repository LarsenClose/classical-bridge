/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Complexity/FoldUnfoldNonclosure.lean — The fold/unfold
asymmetry of classical naming blocks structural sections at the weakest level.

## Main definitions

  FoldUnfoldSection M₁ M₂ — a map preserving fold and unfold (no grade
  condition). Strictly weaker than GRMorphism.

## Main theorems

  fold_unfold_nonclosure — no FoldUnfoldSection from T(classicalGRM h) to
  classicalGRM h when headerLen > 0. Proved from the fold/unfold length
  asymmetry alone.

  naming_cost_nonclosure_from_section — naming_cost_nonclosure (which
  requires the stronger GRMorphism) follows as corollary.

## Proof

The fold/unfold asymmetry of the classical naming convention (fold drops
the header, unfold prepends it) prevents any section from T(M) to M.

For the identity transport t ∈ T(M):
  - T(M).fold t = t  (roundtrip)
  - T(M).unfold = id

A section φ preserving fold and unfold forces:
  - M.fold (φ.map t) = φ.map t   (from map_fold + roundtrip)
  - M.unfold (φ.map t) = φ.map t (from map_unfold + unfold = id)

So fold and unfold agree on φ.map t. But fold shortens by headerLen
and unfold lengthens by headerLen. When headerLen > 0: contradiction.

This is Cannot 2 in its weakest form: even without grade preservation,
the fold/unfold asymmetry of classical naming blocks structural return
from the substrate.

## Why the asymmetry is forced

The fold/unfold asymmetry is not a modeling choice among alternatives.
It is forced by the carrier architecture:

1. Classical computation uses binary strings with a self-application
   header. This is not a choice — it's what TMs do when they run
   programs on their own descriptions.

2. The header forces fold = drop header, unfold = prepend header.
   This gives classicalGRM. The GRM is determined by the computation
   model, not selected from alternatives.

3. The GRM forces the carrier architecture: fold shortens, unfold
   lengthens, selfApp accumulates drift = headerLen.

4. The transport model T(M) is the substrate where selfApp = id.
   Also forced — it's the consequence-closed transports over M.

5. A FoldUnfoldSection from T(M) to M is the weakest structural
   relationship that could witness compatibility between frictionless
   computation and the classical naming convention.

6. The fold/unfold asymmetry makes it impossible. Any map commuting
   with both would require fold and unfold to agree on a point, but
   fold shortens and unfold lengthens when headerLen > 0.

## Relationship to naming_cost_nonclosure (SemanticBridge.lean)

naming_cost_nonclosure proves the nonclosure for GRMorphism (which
requires grade preservation in addition to fold/unfold commutation).
fold_unfold_nonclosure proves it for FoldUnfoldSection (fold/unfold
commutation only). Since GRMorphism is strictly stronger than
FoldUnfoldSection, naming_cost_nonclosure follows as corollary.

## Axiom profile

Zero custom axioms. Uses only propext, Classical.choice, Quot.sound.

STATUS: 0 sorry.
-/

import ClassicalBridge.Complexity.SemanticBridge

namespace ClassicalBridge.Complexity.FoldUnfoldNonclosure

open WTS
open ClassicalBridge.Complexity.SemanticBridge
open ClassicalBridge.Bridge
open ClassicalBridge.TM

-- ════════════════════════════════════════════════════════════
-- Section 1: FoldUnfoldSection — the minimal structural section
-- ════════════════════════════════════════════════════════════

/-- A fold-unfold section between graded reflexive models: a map
    preserving fold and unfold, with no grade condition.

    This is strictly weaker than GRMorphism (which additionally
    requires exact grade preservation) and GRRetraction (which
    requires grade non-increasing). The nonclosure refutation
    works at this level because it depends only on the fold/unfold
    length asymmetry, not on grade compatibility. -/
structure FoldUnfoldSection (M₁ M₂ : WTS.GradedReflModel) where
  /-- The underlying map on carriers. -/
  map : M₁.carrier → M₂.carrier
  /-- Commutes with fold: map(fold₁(x)) = fold₂(map(x)). -/
  map_fold : ∀ x, map (M₁.fold x) = M₂.fold (map x)
  /-- Commutes with unfold: map(unfold₁(x)) = unfold₂(map(x)). -/
  map_unfold : ∀ x, map (M₁.unfold x) = M₂.unfold (map x)

/-- Every WTS.GRMorphism gives a FoldUnfoldSection (forget grade preservation). -/
def FoldUnfoldSection.ofGRMorphism {M₁ M₂ : WTS.GradedReflModel}
    (φ : WTS.GRMorphism M₁ M₂) : FoldUnfoldSection M₁ M₂ where
  map := φ.map
  map_fold := φ.map_fold
  map_unfold := φ.map_unfold

-- ════════════════════════════════════════════════════════════
-- Section 2: Fold/unfold nonclosure
-- ════════════════════════════════════════════════════════════

/-- The fold/unfold asymmetry of classical naming blocks structural
    sections at the weakest level.

    No FoldUnfoldSection from T(classicalGRM h) to classicalGRM h
    when headerLen > 0. No grade condition on the section is needed.
    The contradiction arises purely from the fold/unfold length
    asymmetry of the classical carrier.

    The proof is identical to naming_cost_nonclosure (SemanticBridge.lean)
    but requires only map_fold and map_unfold, not map_grade. -/
theorem fold_unfold_nonclosure (h : SelfAppHeader) (hne : h.headerLen > 0)
    (φ : FoldUnfoldSection (transportGradedReflModel (classicalGRM_WTS h))
                           (classicalGRM_WTS h)) :
    False := by
  set M := classicalGRM_WTS h
  set TM := transportGradedReflModel M
  set t := Transport.identity M
  -- fold_T(t) = t (by roundtrip on the transport model)
  have h_fold_id : TM.fold t = t := TM.roundtrip t
  -- map_fold: φ(fold_T(t)) = fold_M(φ(t)). Since fold_T(t) = t: fold_M(φ(t)) = φ(t)
  have h1 : M.fold (φ.map t) = φ.map t := by
    have := φ.map_fold t; rw [h_fold_id] at this; exact this.symm
  -- map_unfold: φ(unfold_T(t)) = unfold_M(φ(t)). Since unfold_T = id: unfold_M(φ(t)) = φ(t)
  have h2 : M.unfold (φ.map t) = φ.map t := by
    have := φ.map_unfold t; exact this.symm
  -- fold(x) = x = unfold(x), so fold(x) = unfold(x)
  have h_eq : M.fold (φ.map t) = M.unfold (φ.map t) := by rw [h1, h2]
  -- fold shortens or preserves length
  have h_len : List.length (M.fold (φ.map t)) ≤ List.length (φ.map t) := by
    simp [M, classicalGRM_WTS, classicalGRM, classicalAdmissibleEncoding,
          ClassicalBridge.AdmissibleEncoding.toGRM, bridgeFold, canonicalSpec,
          TMSelfAppSpec.fold, tmFold, List.length_drop]
  -- unfold lengthens by headerLen
  have h_len2 : List.length (M.unfold (φ.map t)) ≥
      List.length (φ.map t) + h.headerLen := by
    simp only [M, classicalGRM_WTS, classicalGRM, classicalAdmissibleEncoding,
          ClassicalBridge.AdmissibleEncoding.toGRM, bridgeUnfold, canonicalSpec,
          TMSelfAppSpec.unfold, tmUnfold, List.length_append]
    rw [h.headerLen_eq]; omega
  rw [h_eq] at h_len; omega

-- ════════════════════════════════════════════════════════════
-- Section 3: Corollary — naming_cost_nonclosure follows
-- ════════════════════════════════════════════════════════════

/-- naming_cost_nonclosure is a corollary: GRMorphism is stronger
    than FoldUnfoldSection, so the nonclosure follows a fortiori. -/
theorem naming_cost_nonclosure_from_section (h : SelfAppHeader) (hne : h.headerLen > 0)
    (φ : GRMorphism (transportGradedReflModel (classicalGRM_WTS h))
                     (classicalGRM_WTS h)) :
    False :=
  fold_unfold_nonclosure h hne (FoldUnfoldSection.ofGRMorphism φ)

-- ════════════════════════════════════════════════════════════
-- Section 4: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms fold_unfold_nonclosure
#print axioms naming_cost_nonclosure_from_section

end ClassicalBridge.Complexity.FoldUnfoldNonclosure
