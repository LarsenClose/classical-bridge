/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Bridge/DynamicDriftBridge.lean — Dynamic drift
characterization of classicalGRM.

This file connects the dynamic drift infrastructure from witness-transport
to classicalGRM. The key mathematical fact is:

  classicalGRM.selfApp(x) = header ++ x.drop(headerLen)

For x with grade ≥ headerLen:
  grade(selfApp(x)) = headerLen + (grade(x) - headerLen) = grade(x)
  → drift is exactly 0 at this grade level

For x with grade < headerLen:
  grade(selfApp(x)) = headerLen ≤ grade(x) + bridgeOverhead
  → drift is bounded by bridgeOverhead

This makes classicalGRM an instance of "eventually-zero drift":
above bridgeOverhead, selfApp is grade-preserving.

DESIGN NOTE: The WTS types (EventuallyZeroDrift, EventuallyZeroDriftBounded)
are defined for WTS.GradedReflModel. classicalGRM is a ClassicalBridge.GradedReflModel
(a mirror type). This file defines analogous predicates locally in the
ClassicalBridge namespace, proves classicalGRM satisfies them, and connects
to the existing ClassicalBridge.Reductions.HasFiniteDrift API.

The classicalDynamicDrift function (δ(g) = 0 if g ≥ bridgeOverhead, else
bridgeOverhead) is a valid pointwise DynamicDrift witness — it is NOT the
WTS actualDriftFn (which would be constant at bridgeOverhead everywhere,
because small inputs always force k = bridgeOverhead). The function here is
the tightest pointwise bound, but it is non-increasing across the threshold.

STATUS: 0 sorry.
-/

import ClassicalBridge.Bridge.ChainConnection
import ClassicalBridge.Reductions.KarpPreservation

namespace ClassicalBridge.Bridge

open ClassicalBridge.TM
open ClassicalBridge.Reductions

-- ════════════════════════════════════════════════════════════
-- Section 1: Mirror predicates for ClassicalBridge.GradedReflModel
-- ════════════════════════════════════════════════════════════

/-- A GRM has eventually-zero drift: for all x with grade ≥ threshold,
    selfApp does not increase the grade.

    Mirror of WTS.GradedReflModel.EventuallyZeroDrift, instantiated
    at ClassicalBridge.GradedReflModel. -/
def EventuallyZeroDrift (M : GradedReflModel) (threshold : Nat) : Prop :=
  ∀ x, M.grade x ≥ threshold → M.grade (M.selfApp x) ≤ M.grade x

/-- A GRM has eventually-zero drift AND bounded drift below threshold.

    Above threshold: drift is zero.
    Below threshold: drift is bounded by k.
    Together: uniform finite drift.

    Mirror of WTS.GradedReflModel.EventuallyZeroDriftBounded. -/
def EventuallyZeroDriftBounded (M : GradedReflModel) (threshold k : Nat) : Prop :=
  (∀ x, M.grade x ≥ threshold → M.grade (M.selfApp x) ≤ M.grade x) ∧
  (∀ x, M.grade x < threshold → M.grade (M.selfApp x) ≤ M.grade x + k)

-- ════════════════════════════════════════════════════════════
-- Section 2: EventuallyZeroDriftBounded implies HasFiniteDrift
-- ════════════════════════════════════════════════════════════

/-- EventuallyZeroDriftBounded implies HasFiniteDrift at bound k.

    For inputs above threshold: drift is 0 ≤ k.
    For inputs below threshold: drift is at most k.
    Together: drift ≤ k everywhere.

    Note: HasFiniteDrift E k uses E.grade and E.selfApp; EventuallyZeroDriftBounded
    uses E.toGRM.grade and E.toGRM.selfApp. Since toGRM.grade = E.grade and
    toGRM.selfApp = E.selfApp definitionally, we use `show` to align. -/
theorem eventuallyZeroDriftBounded_finiteDrift
    (E : AdmissibleEncoding) (threshold k : Nat)
    (h : EventuallyZeroDriftBounded E.toGRM threshold k) :
    HasFiniteDrift E k := by
  intro x
  -- AdmissibleEncoding.toGRM uses E.grade and E.selfApp, so definitional eq holds.
  -- Restate goal using toGRM to match h's hypotheses.
  change E.toGRM.grade (E.toGRM.selfApp x) ≤ E.toGRM.grade x + k
  by_cases hge : E.toGRM.grade x ≥ threshold
  · have hle := h.1 x hge; omega
  · simp only [ge_iff_le, Nat.not_le] at hge
    exact h.2 x hge

-- ════════════════════════════════════════════════════════════
-- Section 3: classicalGRM has eventually-zero drift
-- ════════════════════════════════════════════════════════════

/-- classicalGRM has eventually-zero drift at threshold bridgeOverhead.

    For x with grade(x) ≥ bridgeOverhead = headerLen:
      grade(selfApp(x)) = grade(x)  [by classicalGRM_selfApp_grade_large]
    So grade(selfApp(x)) ≤ grade(x). -/
theorem classicalGRM_eventuallyZeroDrift :
    EventuallyZeroDrift classicalGRM bridgeOverhead := by
  intro x hx
  have h := classicalGRM_selfApp_grade_large x hx
  omega

/-- For grade(x) ≥ bridgeOverhead, selfApp preserves grade exactly. -/
theorem classicalGRM_drift_zero_above_threshold (x : BinString)
    (hx : classicalGRM.grade x ≥ bridgeOverhead) :
    classicalGRM.grade (classicalGRM.selfApp x) = classicalGRM.grade x :=
  classicalGRM_selfApp_grade_large x hx

-- ════════════════════════════════════════════════════════════
-- Section 4: classicalGRM satisfies EventuallyZeroDriftBounded
-- ════════════════════════════════════════════════════════════

/-- classicalGRM satisfies EventuallyZeroDriftBounded at (bridgeOverhead, bridgeOverhead).

    Above threshold (grade ≥ bridgeOverhead):
      grade(selfApp(x)) = grade(x) ≤ grade(x)  [zero drift]

    Below threshold (grade < bridgeOverhead):
      grade(selfApp(x)) ≤ bridgeOverhead ≤ grade(x) + bridgeOverhead  [bounded drift] -/
theorem classicalGRM_eventuallyZeroDriftBounded :
    EventuallyZeroDriftBounded classicalGRM bridgeOverhead bridgeOverhead := by
  refine ⟨?_, ?_⟩
  · -- Above threshold: drift is 0
    intro x hx
    have h := classicalGRM_selfApp_grade_large x hx
    omega
  · -- Below threshold: grade(selfApp(x)) ≤ bridgeOverhead ≤ grade(x) + bridgeOverhead
    intro x hx
    have h := classicalGRM_selfApp_grade_small x hx
    omega

-- ════════════════════════════════════════════════════════════
-- Section 5: A dynamic drift function for classicalGRM
-- ════════════════════════════════════════════════════════════

/-- A pointwise dynamic drift witness for classicalGRM:
      classicalDynamicDrift(g) = 0 if g ≥ bridgeOverhead
      classicalDynamicDrift(g) = bridgeOverhead otherwise

    This is a valid DynamicDrift witness in the sense of
    WTS.GradedReflModel.DynamicDriftCompatibleExtension:
      grade(selfApp(x)) ≤ grade(x) + classicalDynamicDrift(grade(x))   for all x.

    NOTE: This function is non-increasing across the threshold (it drops from
    bridgeOverhead to 0). It is NOT the WTS actualDriftFn, which would be the
    least constant bound at each grade level (constant = bridgeOverhead for all g,
    because any grade-g bound must cover the grade-0 inputs that map to grade
    bridgeOverhead). classicalDynamicDrift is the tightest POINTWISE bound but
    it does not accumulate over smaller grades.

    Noncomputable because bridgeOverhead depends on classical_selfapp_header_exists. -/
noncomputable def classicalDynamicDrift (g : Nat) : Nat :=
  if g ≥ bridgeOverhead then 0 else bridgeOverhead

/-- classicalDynamicDrift witnesses the pointwise drift bound for classicalGRM. -/
theorem classicalGRM_dynamicDrift_bound (x : BinString) :
    classicalGRM.grade (classicalGRM.selfApp x) ≤
    classicalGRM.grade x + classicalDynamicDrift (classicalGRM.grade x) := by
  simp only [classicalDynamicDrift]
  split_ifs with hge
  · -- grade(x) ≥ bridgeOverhead: drift is 0, grade is preserved exactly
    simp only [Nat.add_zero]
    exact Nat.le_of_eq (classicalGRM_selfApp_grade_large x hge)
  · -- grade(x) < bridgeOverhead: grade(selfApp(x)) ≤ bridgeOverhead ≤ grade(x) + bridgeOverhead
    simp only [ge_iff_le, Nat.not_le] at hge
    have hsmall := classicalGRM_selfApp_grade_small x hge
    omega

/-- In the zero-drift region (grade ≥ bridgeOverhead), classicalDynamicDrift is 0. -/
theorem classicalDynamicDrift_zero_above (g : Nat) (hg : g ≥ bridgeOverhead) :
    classicalDynamicDrift g = 0 := by
  simp [classicalDynamicDrift, hg]

/-- In the positive-drift region (grade < bridgeOverhead), classicalDynamicDrift
    equals bridgeOverhead. -/
theorem classicalDynamicDrift_overhead_below (g : Nat) (hg : g < bridgeOverhead) :
    classicalDynamicDrift g = bridgeOverhead := by
  simp only [classicalDynamicDrift]
  have : ¬(g ≥ bridgeOverhead) := Nat.not_le.mpr hg
  simp [this]

-- ════════════════════════════════════════════════════════════
-- Section 6: Connection between EventuallyZeroDrift and HasFiniteDrift
-- ════════════════════════════════════════════════════════════

/-- classicalGRM has finite drift at bridgeOverhead.

    This is derived from EventuallyZeroDriftBounded, making explicit the
    two-case structure: small inputs (drift ≤ bridgeOverhead) and large
    inputs (drift = 0). -/
theorem classicalGRM_finiteDrift_from_eventuallyZero :
    HasFiniteDrift classicalAdmissibleEncoding bridgeOverhead :=
  eventuallyZeroDriftBounded_finiteDrift classicalAdmissibleEncoding
    bridgeOverhead bridgeOverhead
    classicalGRM_eventuallyZeroDriftBounded

/-- classicalGRM admits the classicalDynamicDrift witness:
    grade(selfApp(x)) ≤ grade(x) + classicalDynamicDrift(grade(x)) for all x. -/
theorem classicalGRM_admits_dynamicDrift :
    ∀ x : BinString,
      classicalGRM.grade (classicalGRM.selfApp x) ≤
      classicalGRM.grade x + classicalDynamicDrift (classicalGRM.grade x) :=
  classicalGRM_dynamicDrift_bound

-- ════════════════════════════════════════════════════════════
-- Section 7: Explicit region characterizations
-- ════════════════════════════════════════════════════════════

/-- Zero-drift region: selfApp is grade-preserving above bridgeOverhead. -/
theorem classicalGRM_selfApp_grade_preserving_above
    (x : BinString) (hx : classicalGRM.grade x ≥ bridgeOverhead) :
    classicalGRM.grade (classicalGRM.selfApp x) = classicalGRM.grade x :=
  classicalGRM_selfApp_grade_large x hx

/-- Bounded-drift region: selfApp grade is bounded above by bridgeOverhead. -/
theorem classicalGRM_selfApp_grade_bounded_below
    (x : BinString) (hx : classicalGRM.grade x < bridgeOverhead) :
    classicalGRM.grade (classicalGRM.selfApp x) ≤ bridgeOverhead :=
  classicalGRM_selfApp_grade_small x hx

-- ════════════════════════════════════════════════════════════
-- Section 8: Summary theorem
-- ════════════════════════════════════════════════════════════

/-- Complete dynamic drift characterization of classicalGRM.

    (1) EventuallyZeroDrift at bridgeOverhead:
        grade(x) ≥ bridgeOverhead → grade(selfApp(x)) ≤ grade(x)  [in fact equal]

    (2) EventuallyZeroDriftBounded at (bridgeOverhead, bridgeOverhead):
        above: drift = 0; below: drift ≤ bridgeOverhead

    (3) classicalDynamicDrift is a valid pointwise dynamic drift witness:
        grade(selfApp(x)) ≤ grade(x) + classicalDynamicDrift(grade(x))

    (4) HasFiniteDrift at bridgeOverhead (derived from the dynamic structure) -/
theorem classicalGRM_dynamic_drift_summary :
    EventuallyZeroDrift classicalGRM bridgeOverhead ∧
    EventuallyZeroDriftBounded classicalGRM bridgeOverhead bridgeOverhead ∧
    (∀ x : BinString, classicalGRM.grade (classicalGRM.selfApp x) ≤
      classicalGRM.grade x + classicalDynamicDrift (classicalGRM.grade x)) ∧
    HasFiniteDrift classicalAdmissibleEncoding bridgeOverhead :=
  ⟨classicalGRM_eventuallyZeroDrift,
   classicalGRM_eventuallyZeroDriftBounded,
   classicalGRM_dynamicDrift_bound,
   classicalGRM_finiteDrift_from_eventuallyZero⟩

-- ════════════════════════════════════════════════════════════
-- Axiom audit
-- ════════════════════════════════════════════════════════════

/-
AXIOM INVENTORY for DynamicDriftBridge.lean:

Custom axioms (inherited transitively from UniversalSimulation.lean):
1. classical_tm_exists : StepBoundedTM
2. classical_selfapp_header_exists : SelfAppHeader

Standard Lean axioms: propext, Quot.sound (from list operations).

All theorems in this file are PROVED, not axiomatized.
The proofs use:
- classicalGRM_selfApp_grade_large (from ChainConnection.lean)
- classicalGRM_selfApp_grade_small (from ChainConnection.lean)
- Basic arithmetic (omega)

No additional axioms beyond those already used by ChainConnection.lean.
-/

#check @classicalGRM_eventuallyZeroDrift
#check @classicalGRM_eventuallyZeroDriftBounded
#check @classicalGRM_dynamicDrift_bound
#check @classicalGRM_dynamic_drift_summary

end ClassicalBridge.Bridge
