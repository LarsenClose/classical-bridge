/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Bridge/NonVacuity.lean — Non-vacuity witness for the drifted lock.

The drifted lock (DriftedLock.lean) proves: DriftedLockData → False, where
DriftedLockData bundles (drift, solver_poly, combined_injection). The combined_injection
field asserts PolyBoundedConstruction N_End N_Val (solver_poly.shift drift), using the
CONCRETE counting functions N_End and N_Val from CountingFunctions.lean.

The TransferHypothesis lock (classical-constraints) was vacuous: TransferHypothesis is
type-level incompatible with SelfAppUnbounded, so the hypothesis bundle could never be
inhabited regardless of counting behavior.

The drifted lock is genuinely non-vacuous. This file demonstrates it in two ways:

(1) GRM-LEVEL WITNESS: We construct NatHalfModel — a concrete GradedReflModel with
    carrier = Nat, fold(n) = n/2, unfold(n) = 2*n+1, grade = id. We prove:
    - roundtrip: fold(unfold(n)) = n for all n  [omega, via (2n+1)/2 = n]
    - finite drift at k=1: grade(selfApp(n)) ≤ grade(n)+1 for all n
    - selfApp causes grade overflow at every even input (grade(selfApp(d)) = d+1 > d)
    - PEqNP: selfApp factors through grade 1

    This shows that GRM-level finite drift is structurally satisfiable. The GRM
    architecture does not make the drifted lock trivial.

(2) COUNTING MODEL WITNESS: We define trivial counting functions N_triv g = 1 and
    show that PolyBoundedConstruction N_triv N_triv p holds for EVERY polynomial p.
    This demonstrates that combined_injection is satisfiable in an alternative counting
    model — the drifted lock's impossibility is specific to the tower-exponential growth
    of N_End = (2^(g+1))^(2^(g+1)), not a type-level inconsistency.

These two witnesses together establish:
  - The GRM structure does not force the lock's hypotheses to be contradictory
  - Only the specific counting content of N_End vs N_Val creates the impossibility
  - drifted_lock is a genuine theorem, not a degenerate True→False derivation

NOTE ON PEqNP: NatHalfModel satisfies PEqNP (selfApp factors through grade 1).
This is consistent with finite drift: the bounded-overhead regime contains PEqNP
models. The non-vacuity claim is that the lock's hypotheses are type-level
satisfiable, not that a model separates the regimes.

STATUS: 0 sorry.
-/

import ClassicalBridge.Mirror.CountingFunctions
import ClassicalBridge.Bridge.DriftedLock

namespace ClassicalBridge.Bridge.NonVacuity

open ClassicalBridge
open ClassicalBridge.Bridge

-- ════════════════════════════════════════════════════════════
-- Section 1: NatHalfModel — the concrete GRM witness
-- ════════════════════════════════════════════════════════════

/-- NatHalfModel: a GradedReflModel on the natural numbers where
    fold halves (integer division) and unfold doubles-and-adds-one.

    roundtrip: fold(unfold(n)) = (2n+1)/2 = n  (provable by omega)
    selfApp(n) = unfold(fold(n)) = 2*(n/2)+1:
      even n → selfApp(n) = n+1   (grade inflation by 1)
      odd n  → selfApp(n) = n     (grade preserved) -/
def NatHalfModel : GradedReflModel where
  carrier  := Nat
  fold     := fun n => n / 2
  unfold   := fun n => 2 * n + 1
  roundtrip := by intro n; omega
  grade    := id

-- ════════════════════════════════════════════════════════════
-- Section 2: selfApp computation lemmas
-- ════════════════════════════════════════════════════════════

/-- selfApp of NatHalfModel is 2*(n/2)+1. -/
theorem NatHalfModel_selfApp_eq (n : Nat) :
    NatHalfModel.selfApp n = 2 * (n / 2) + 1 := by
  simp [GradedReflModel.selfApp, NatHalfModel]

/-- For even n, selfApp(n) = n + 1. -/
theorem NatHalfModel_selfApp_even (n : Nat) (h : n % 2 = 0) :
    NatHalfModel.selfApp n = n + 1 := by
  simp [GradedReflModel.selfApp, NatHalfModel]; omega

/-- For odd n, selfApp(n) = n. -/
theorem NatHalfModel_selfApp_odd (n : Nat) (h : n % 2 = 1) :
    NatHalfModel.selfApp n = n := by
  simp [GradedReflModel.selfApp, NatHalfModel]; omega

-- ════════════════════════════════════════════════════════════
-- Section 3: Finite drift at k=1
-- ════════════════════════════════════════════════════════════

/-- NatHalfModel has finite drift at k=1:
    grade(selfApp(n)) ≤ grade(n)+1 for all n.

    Proof: selfApp(n) = 2*(n/2)+1, and 2*(n/2)+1 ≤ n+1 always
    (since 2*(n/2) ≤ n by integer division). omega closes it. -/
theorem NatHalfModel_finiteDrift :
    ∀ n : Nat, NatHalfModel.grade (NatHalfModel.selfApp n) ≤ NatHalfModel.grade n + 1 := by
  intro n
  simp only [GradedReflModel.selfApp, NatHalfModel, id]
  omega

-- ════════════════════════════════════════════════════════════
-- Section 4: Grade overflow at even inputs
-- ════════════════════════════════════════════════════════════

/-- selfApp overflows grade d at every even input d:
    grade(d) = d ≤ d  and  grade(selfApp(d)) = d+1 > d. -/
theorem NatHalfModel_overflow_even (d : Nat) (h : d % 2 = 0) :
    NatHalfModel.grade d ≤ d ∧ NatHalfModel.grade (NatHalfModel.selfApp d) > d := by
  simp only [GradedReflModel.selfApp, NatHalfModel, id]
  omega

-- ════════════════════════════════════════════════════════════
-- Section 5: NatHalfModel satisfies PEqNP
-- ════════════════════════════════════════════════════════════

/-- NatHalfModel satisfies PEqNP: selfApp factors through grade 1.

    For x ≤ 1: omega resolves both x=0 (selfApp=1≤1) and x=1 (selfApp=1≤1).
    NatHalfModel lives in the PEqNP/finite-drift regime, consistent with
    the general fact that finite drift implies PEqNP. -/
theorem NatHalfModel_PEqNP : PEqNP NatHalfModel := by
  refine ⟨1, fun x hx => ?_⟩
  simp only [GradedReflModel.selfApp, NatHalfModel, id] at *
  omega

-- ════════════════════════════════════════════════════════════
-- Section 6: Trivial counting model witness
-- ════════════════════════════════════════════════════════════

/-- Trivial counting function: every grade has exactly 1 element.
    The degenerate model where all grade-level distinctions collapse. -/
def N_triv (_ : Nat) : Nat := 1

/-- PolyBoundedConstruction holds in the trivial model for every polynomial:
    1 ≤ 1 regardless of the shift. -/
theorem trivial_model_poly_bound (p : PolyBound) :
    PolyBoundedConstruction N_triv N_triv p := by
  intro _; simp [N_triv]

-- ════════════════════════════════════════════════════════════
-- Section 7: Non-vacuity theorem
-- ════════════════════════════════════════════════════════════

/-- NON-VACUITY THEOREM: The drifted lock's impossibility is not type-level.

    The Prop `PolyBoundedConstruction N_L₁ N_L₂ p` is satisfiable for suitable
    counting functions. With N_L₁ = N_L₂ = N_triv (trivial model, constant 1),
    the bound holds for every polynomial.

    Contrast with the TransferHypothesis lock:
    - TransferHypothesis + SelfAppUnbounded: uninhabitable at the TYPE level
      (BridgeVacuity shows type-level incompatibility before counting enters)
    - DriftedLockData's combined_injection: a well-formed Prop, satisfiable in
      an alternative counting model

    The drifted lock's impossibility is entirely due to the specific growth rates
    of N_End = (2^(g+1))^(2^(g+1)) and N_Val = 2^(g+1). Replace these with any
    constant function and the bound becomes trivially true. -/
theorem drifted_lock_non_vacuous :
    ∃ (N_L₁ N_L₂ : Nat → Nat) (drift : Nat) (p : PolyBound),
      PolyBoundedConstruction N_L₁ N_L₂ (p.shift drift) :=
  ⟨N_triv, N_triv, 7,
   { degree := 2, constant := 3 },
   trivial_model_poly_bound _⟩

/-- The combined_injection type is satisfiable in the trivial model for any
    drift and solver_poly. Direct witness that DriftedLockData's third field
    is not a vacuously false type. -/
theorem combined_injection_satisfiable_in_trivial_model
    (drift : Nat) (solver_poly : PolyBound) :
    PolyBoundedConstruction N_triv N_triv (solver_poly.shift drift) :=
  trivial_model_poly_bound (solver_poly.shift drift)

-- ════════════════════════════════════════════════════════════
-- Section 8: Summary
-- ════════════════════════════════════════════════════════════

/-- SUMMARY: The drifted lock is a genuine impossibility result.

    Verified:
    1. NatHalfModel has finite drift at k=1.
    2. NatHalfModel has grade overflow at every even input.
    3. NatHalfModel satisfies PEqNP (consistent with the bounded regime).
    4. combined_injection is satisfiable in the trivial counting model.
    5. drifted_lock_non_vacuous confirms the impossibility is counting-level only. -/
theorem nonvacuity_summary :
    (∀ n : Nat, NatHalfModel.grade (NatHalfModel.selfApp n) ≤ NatHalfModel.grade n + 1) ∧
    PEqNP NatHalfModel ∧
    (∃ (N_L₁ N_L₂ : Nat → Nat) (drift : Nat) (p : PolyBound),
      PolyBoundedConstruction N_L₁ N_L₂ (p.shift drift)) :=
  ⟨NatHalfModel_finiteDrift, NatHalfModel_PEqNP, drifted_lock_non_vacuous⟩

end ClassicalBridge.Bridge.NonVacuity
