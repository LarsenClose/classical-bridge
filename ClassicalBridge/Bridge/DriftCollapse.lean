/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Bridge/DriftCollapse.lean — Abstract conditions under which
a GRM's drift function δ(g) becomes eventually zero.

The classicalGRM case is the template: above headerLen, selfApp is
grade-preserving (drift = 0), because fold and unfold are mutual inverses
at the grade level. Below headerLen, selfApp grade is bounded by headerLen.
The abstract question: what structural properties of fold/unfold force this?

Two structural conditions:

  (A) GradePreservingAbove t:
      ∀ x, grade(x) ≥ t → grade(selfApp(x)) = grade(x)

  (B) SelfAppBoundedBelow t k:
      ∀ x, grade(x) < t → grade(selfApp(x)) ≤ k

  (C) AdditiveOverheadBound c:
      ∀ x, grade(selfApp(x)) ≤ grade(x) + c  (constant drift)

KEY RESULTS (all proved, 0 sorry):
  - (A) → EventuallyZeroDrift at t
  - (A) + (B) → EventuallyZeroDriftBounded at (t, k) → FiniteDrift
  - (A) + (B) with t = k → AdditiveOverheadBound k
  - (C) ↔ FiniteDrift at c
  - fold adds ≤ c₁, unfold adds ≤ c₂ → selfApp adds ≤ c₁ + c₂
  - roundtrip axiom: grade(fold(unfold(x))) = grade(x) exactly
  - fold and unfold both grade-non-decreasing + EventuallyZeroDrift → (A)
  - ExactRetraction structure → (A)
  - classicalGRM satisfies all three conditions

STATUS: 0 sorry.
-/

import ClassicalBridge.Bridge.DynamicDriftBridge

-- ════════════════════════════════════════════════════════════
-- Section 1: Abstract structural conditions on GradedReflModel
-- Defined in ClassicalBridge namespace for dot-notation resolution.
-- ════════════════════════════════════════════════════════════

namespace ClassicalBridge

/-- Condition (A): selfApp is grade-preserving above threshold t.
    This is the structural property forcing drift collapse:
    self-application cannot change description complexity above the threshold. -/
def GradedReflModel.GradePreservingAbove (M : GradedReflModel) (t : Nat) : Prop :=
  ∀ x, M.grade x ≥ t → M.grade (M.selfApp x) = M.grade x

/-- Condition (B): selfApp grade is bounded by k for all inputs below threshold t. -/
def GradedReflModel.SelfAppBoundedBelow (M : GradedReflModel) (t k : Nat) : Prop :=
  ∀ x, M.grade x < t → M.grade (M.selfApp x) ≤ k

/-- Condition (C): selfApp adds at most c to grade everywhere (constant drift).
    Equivalent to FiniteDrift at c. -/
def GradedReflModel.AdditiveOverheadBound (M : GradedReflModel) (c : Nat) : Prop :=
  ∀ x, M.grade (M.selfApp x) ≤ M.grade x + c

/-- fold adds at most c to grade. -/
def GradedReflModel.FoldAdditiveOverhead (M : GradedReflModel) (c : Nat) : Prop :=
  ∀ x, M.grade (M.fold x) ≤ M.grade x + c

/-- unfold adds at most c to grade. -/
def GradedReflModel.UnfoldAdditiveOverhead (M : GradedReflModel) (c : Nat) : Prop :=
  ∀ x, M.grade (M.unfold x) ≤ M.grade x + c

end ClassicalBridge

-- ════════════════════════════════════════════════════════════
-- Sections 2–9: Theorems about drift collapse
-- ════════════════════════════════════════════════════════════

namespace ClassicalBridge.Bridge

open ClassicalBridge
open ClassicalBridge.TM
open ClassicalBridge.Reductions

-- ════════════════════════════════════════════════════════════
-- Section 2: Condition (A) implies EventuallyZeroDrift
-- ════════════════════════════════════════════════════════════

/-- Condition (A) implies EventuallyZeroDrift at t.
    Grade preservation above t (equality) implies ≤ above t. -/
theorem gradePreservingAbove_implies_eventuallyZeroDrift
    (M : GradedReflModel) {t : Nat}
    (hA : M.GradePreservingAbove t) :
    EventuallyZeroDrift M t :=
  fun x hx => Nat.le_of_eq (hA x hx)

-- ════════════════════════════════════════════════════════════
-- Section 3: (A) + (B) → EventuallyZeroDriftBounded → FiniteDrift
-- ════════════════════════════════════════════════════════════

/-- (A) + (B) → EventuallyZeroDriftBounded at (t, k).
    Above t: grade(selfApp(x)) = grade(x) ≤ grade(x).
    Below t: grade(selfApp(x)) ≤ k ≤ grade(x) + k. -/
theorem gradePreserving_and_bounded_eventuallyZeroDriftBounded
    (M : GradedReflModel) {t k : Nat}
    (hA : M.GradePreservingAbove t)
    (hB : M.SelfAppBoundedBelow t k) :
    EventuallyZeroDriftBounded M t k :=
  ⟨fun x hx => Nat.le_of_eq (hA x hx),
   fun x hx => Nat.le_trans (hB x hx) (Nat.le_add_left k _)⟩

/-- (A) + (B) → FiniteDrift. -/
theorem gradePreserving_and_bounded_finiteDrift
    (M : GradedReflModel) {t k : Nat}
    (hA : M.GradePreservingAbove t)
    (hB : M.SelfAppBoundedBelow t k) :
    ∃ c, ∀ x, M.grade (M.selfApp x) ≤ M.grade x + c :=
  ⟨k, fun x => by
    by_cases hge : M.grade x ≥ t
    · have := hA x hge; omega
    · simp only [ge_iff_le, Nat.not_le] at hge
      exact Nat.le_trans (hB x hge) (Nat.le_add_left k _)⟩

/-- When (A) and (B) hold at the same constant k, selfApp adds at most k everywhere.
    This matches classicalGRM: threshold = bound = bridgeOverhead. -/
theorem gradePreserving_and_bounded_same_threshold
    (M : GradedReflModel) {k : Nat}
    (hA : M.GradePreservingAbove k)
    (hB : M.SelfAppBoundedBelow k k) :
    M.AdditiveOverheadBound k := by
  intro x
  by_cases hge : M.grade x ≥ k
  · have := hA x hge; omega
  · simp only [ge_iff_le, Nat.not_le] at hge
    exact Nat.le_trans (hB x hge) (Nat.le_add_left k _)

-- ════════════════════════════════════════════════════════════
-- Section 4: Condition (C) ↔ FiniteDrift
-- ════════════════════════════════════════════════════════════

/-- Condition (C) at c is the FiniteDrift statement at c. -/
theorem additiveOverheadBound_iff_finiteDrift_at (M : GradedReflModel) (c : Nat) :
    M.AdditiveOverheadBound c ↔
    ∀ x, M.grade (M.selfApp x) ≤ M.grade x + c :=
  Iff.rfl

/-- Condition (C) implies FiniteDrift. -/
theorem additiveOverheadBound_implies_finiteDrift
    (M : GradedReflModel) {c : Nat}
    (hC : M.AdditiveOverheadBound c) :
    ∃ k, ∀ x, M.grade (M.selfApp x) ≤ M.grade x + k :=
  ⟨c, hC⟩

/-- FiniteDrift implies AdditiveOverheadBound at the witnessing constant. -/
theorem finiteDrift_implies_additiveOverheadBound
    (M : GradedReflModel) {k : Nat}
    (hfd : ∀ x, M.grade (M.selfApp x) ≤ M.grade x + k) :
    M.AdditiveOverheadBound k :=
  hfd

-- ════════════════════════════════════════════════════════════
-- Section 5: Fold/unfold overhead composition
-- ════════════════════════════════════════════════════════════

/-- If fold adds ≤ c₁ and unfold adds ≤ c₂, then selfApp adds ≤ c₁ + c₂.

    Pipeline: grade(unfold(fold(x))) ≤ grade(fold(x)) + c₂ ≤ grade(x) + c₁ + c₂. -/
theorem fold_unfold_pipeline_overhead
    (M : GradedReflModel) {c₁ c₂ : Nat}
    (hfold : M.FoldAdditiveOverhead c₁)
    (hunfold : M.UnfoldAdditiveOverhead c₂) :
    M.AdditiveOverheadBound (c₁ + c₂) := by
  intro x
  show M.grade (M.unfold (M.fold x)) ≤ M.grade x + (c₁ + c₂)
  have h1 := hfold x
  have h2 := hunfold (M.fold x)
  omega

/-- The roundtrip axiom gives grade(fold(unfold(x))) = grade(x).
    fold(unfold(·)) is zero-overhead. -/
theorem roundtrip_grade_exact (M : GradedReflModel) (x : M.carrier) :
    M.grade (M.fold (M.unfold x)) = M.grade x := by
  rw [M.roundtrip]

-- ════════════════════════════════════════════════════════════
-- Section 6: Exact retraction → condition (A)
-- ════════════════════════════════════════════════════════════

/-- An "exact retraction" structure implies GradePreservingAbove.

    If above threshold t, fold drops grade by exactly `overhead`:
      grade(x) = grade(fold(x)) + overhead
    And unfold always adds exactly `overhead`:
      grade(unfold(y)) = grade(y) + overhead
    Then grade(unfold(fold(x))) = grade(fold(x)) + overhead = grade(x) for x ≥ t.

    This is the classicalGRM pattern: fold strips headerLen bits,
    unfold prepends them. -/
theorem exact_retraction_implies_gradePreservingAbove
    (M : GradedReflModel) {t overhead : Nat}
    (hfold_exact : ∀ x, M.grade x ≥ t → M.grade x = M.grade (M.fold x) + overhead)
    (hunfold_exact : ∀ y, M.grade (M.unfold y) = M.grade y + overhead) :
    M.GradePreservingAbove t := by
  intro x hx
  show M.grade (M.unfold (M.fold x)) = M.grade x
  rw [hunfold_exact (M.fold x)]
  have := hfold_exact x hx
  omega

-- ════════════════════════════════════════════════════════════
-- Section 7: Grade-monotone fold/unfold + EventuallyZeroDrift → (A)
-- ════════════════════════════════════════════════════════════

/-- If fold and unfold are both grade-non-decreasing, and EventuallyZeroDrift
    holds at t, then GradePreservingAbove t holds.

    Proof: grade(selfApp(x)) = grade(unfold(fold(x)))
             ≥ grade(fold(x))   [unfold non-decreasing]
             ≥ grade(x)         [fold non-decreasing]
    Combined with EventuallyZeroDrift (≤): equality. -/
theorem monotone_fold_unfold_eventuallyZeroDrift_gradePreservingAbove
    (M : GradedReflModel) {t : Nat}
    (hfold_mono : ∀ x, M.grade (M.fold x) ≥ M.grade x)
    (hunfold_mono : ∀ y, M.grade (M.unfold y) ≥ M.grade y)
    (hezd : EventuallyZeroDrift M t) :
    M.GradePreservingAbove t := by
  intro x hx
  -- GradePreservingAbove unfolds to: grade(selfApp(x)) = grade(x)
  -- selfApp x = unfold(fold(x)) by definition
  have hle := hezd x hx   -- grade(selfApp(x)) ≤ grade(x)
  simp only [GradedReflModel.selfApp] at hle
  -- Now hle : M.grade (M.unfold (M.fold x)) ≤ M.grade x
  have h1 : M.grade (M.unfold (M.fold x)) ≥ M.grade (M.fold x) :=
    hunfold_mono (M.fold x)
  have h2 : M.grade (M.fold x) ≥ M.grade x := hfold_mono x
  -- Goal: M.grade (M.selfApp x) = M.grade x
  simp only [GradedReflModel.selfApp]
  omega

-- ════════════════════════════════════════════════════════════
-- Section 8: classicalGRM satisfies the abstract conditions
-- ════════════════════════════════════════════════════════════

/-- classicalGRM satisfies (A): selfApp is grade-preserving above bridgeOverhead. -/
theorem classicalGRM_gradePreservingAbove :
    classicalGRM.GradePreservingAbove bridgeOverhead :=
  fun x hx => classicalGRM_drift_zero_above_threshold x hx

/-- classicalGRM satisfies (B): selfApp grade ≤ bridgeOverhead for small inputs. -/
theorem classicalGRM_selfAppBoundedBelow :
    classicalGRM.SelfAppBoundedBelow bridgeOverhead bridgeOverhead :=
  fun x hx => classicalGRM_selfApp_grade_bounded_below x hx

/-- classicalGRM satisfies (C): selfApp adds at most bridgeOverhead everywhere. -/
theorem classicalGRM_additiveOverheadBound :
    classicalGRM.AdditiveOverheadBound bridgeOverhead :=
  fun x => bridge_selfApp_bounded x

-- ════════════════════════════════════════════════════════════
-- Section 9: Summary
-- ════════════════════════════════════════════════════════════

/-- Complete drift collapse characterization for classicalGRM.
    It satisfies all three abstract conditions at threshold/bound bridgeOverhead. -/
theorem classicalGRM_drift_collapse_summary :
    classicalGRM.GradePreservingAbove bridgeOverhead ∧
    classicalGRM.SelfAppBoundedBelow bridgeOverhead bridgeOverhead ∧
    EventuallyZeroDriftBounded classicalGRM bridgeOverhead bridgeOverhead ∧
    classicalGRM.AdditiveOverheadBound bridgeOverhead :=
  ⟨classicalGRM_gradePreservingAbove,
   classicalGRM_selfAppBoundedBelow,
   gradePreserving_and_bounded_eventuallyZeroDriftBounded
     classicalGRM classicalGRM_gradePreservingAbove classicalGRM_selfAppBoundedBelow,
   classicalGRM_additiveOverheadBound⟩

/-- Any GRM satisfying (A) and (B) has FiniteDrift — the abstract version
    of the classicalGRM finite-drift theorem. -/
theorem abstract_drift_stabilization
    (M : GradedReflModel) {t k : Nat}
    (hA : M.GradePreservingAbove t)
    (hB : M.SelfAppBoundedBelow t k) :
    ∃ c, ∀ x, M.grade (M.selfApp x) ≤ M.grade x + c :=
  gradePreserving_and_bounded_finiteDrift M hA hB

-- ════════════════════════════════════════════════════════════
-- Axiom audit
-- ════════════════════════════════════════════════════════════

#check @GradedReflModel.GradePreservingAbove
#check @GradedReflModel.SelfAppBoundedBelow
#check @GradedReflModel.AdditiveOverheadBound
#check @gradePreservingAbove_implies_eventuallyZeroDrift
#check @gradePreserving_and_bounded_eventuallyZeroDriftBounded
#check @gradePreserving_and_bounded_finiteDrift
#check @gradePreserving_and_bounded_same_threshold
#check @additiveOverheadBound_implies_finiteDrift
#check @fold_unfold_pipeline_overhead
#check @roundtrip_grade_exact
#check @exact_retraction_implies_gradePreservingAbove
#check @monotone_fold_unfold_eventuallyZeroDrift_gradePreservingAbove
#check @classicalGRM_gradePreservingAbove
#check @classicalGRM_selfAppBoundedBelow
#check @classicalGRM_additiveOverheadBound
#check @classicalGRM_drift_collapse_summary
#check @abstract_drift_stabilization

end ClassicalBridge.Bridge
