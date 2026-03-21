/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/TuringMachine/ConcreteModel.lean — Concrete construction of
a StepBoundedTM using Mathlib's Nat.Partrec.Code.evaln.

This file constructs classical_tm : StepBoundedTM, an explicit
inhabitant built on top of Goedel-numbered partial recursive codes.
Used directly by canonicalSpec in UniversalSimulation.lean.

STRATEGY:
  1. Encode BinString → ℕ via a sentinel-based bijection (bitsToNat).
  2. Decode ℕ → BinString via natToBits (any total function suffices).
  3. Define concreteRun by running Nat.Partrec.Code.evaln.
  4. Prove run_zero from the definition of evaln at 0 steps.
  5. Prove run_mono from Mathlib's Nat.Partrec.Code.evaln_mono.
  6. Bundle as classical_tm : StepBoundedTM.

STATUS: Complete. 0 sorry.
-/

import Mathlib.Computability.PartrecCode
import ClassicalBridge.TuringMachine.Basic

namespace ClassicalBridge.TM

-- ════════════════════════════════════════════════════════════
-- Section 1: BinString ↔ ℕ encoding
-- ════════════════════════════════════════════════════════════

/-- Sentinel-based encoding of binary strings as natural numbers.
    [] ↦ 0
    (b :: bs) ↦ 2 * bitsToNat bs + (if b then 2 else 1)

    This is injective: the sentinel bit 1 at the most-significant
    position distinguishes the empty string from all non-empty strings,
    and the bit value distinguishes true from false at each position. -/
def bitsToNat : BinString → ℕ
  | []       => 0
  | b :: bs  => 2 * bitsToNat bs + (if b then 2 else 1)

/-- Decode a natural number back to a binary string.
    natToBits n produces SOME binary string for every n.
    It does not need to be the inverse of bitsToNat —
    we only need it to be total for the StepBoundedTM output. -/
def natToBits : ℕ → BinString
  | 0     => []
  | n + 1 =>
    let b  := (n + 1) % 2 == 1
    let n' := (n + 1) / 2
    b :: natToBits n'
termination_by n => n
decreasing_by
  simp_wf
  omega

-- ════════════════════════════════════════════════════════════
-- Section 2: The concrete run function
-- ════════════════════════════════════════════════════════════

/-- Run a program (encoded as a BinString) on an input (encoded as a BinString)
    for at most `steps` steps, using Goedel-numbered partial recursive codes.

    The program is decoded as:
      code := Nat.Partrec.Code.ofNatCode (bitsToNat prog)

    The input is decoded as:
      input_nat := bitsToNat input

    We run `Nat.Partrec.Code.evaln steps code input_nat` and map the
    resulting ℕ output back through natToBits. -/
def concreteRun (prog input : BinString) (steps : ℕ) : Option BinString :=
  let code      := Nat.Partrec.Code.ofNatCode (bitsToNat prog)
  let input_nat := bitsToNat input
  (Nat.Partrec.Code.evaln steps code input_nat).map natToBits

-- ════════════════════════════════════════════════════════════
-- Section 3: Proof of run_zero
-- ════════════════════════════════════════════════════════════

/-- Zero steps always returns none.
    This follows directly from the definition of evaln: the first pattern
    is `evaln 0 _ _ = none`. -/
theorem concreteRun_zero (p x : BinString) : concreteRun p x 0 = none := by
  simp [concreteRun, Nat.Partrec.Code.evaln]

-- ════════════════════════════════════════════════════════════
-- Section 4: Proof of run_mono
-- ════════════════════════════════════════════════════════════

/-- Monotonicity: if the run halts at t₁ steps, it halts with the same
    result at any t₂ ≥ t₁.

    We unfold the Option.map and use Nat.Partrec.Code.evaln_mono, which
    states: k₁ ≤ k₂ → x ∈ evaln k₁ c n → x ∈ evaln k₂ c n,
    where `x ∈ (o : Option ℕ)` means `o = some x`. -/
theorem concreteRun_mono (p x : BinString) (t₁ t₂ : ℕ) (v : BinString)
    (h : concreteRun p x t₁ = some v) (hle : t₁ ≤ t₂) :
    concreteRun p x t₂ = some v := by
  simp only [concreteRun] at h ⊢
  -- h : (evaln t₁ code input_nat).map natToBits = some v
  -- Goal: (evaln t₂ code input_nat).map natToBits = some v
  rw [Option.map_eq_some_iff] at h ⊢
  obtain ⟨a, ha_mem, ha_eq⟩ := h
  -- ha_mem : evaln t₁ code input_nat = some a
  -- ha_eq  : natToBits a = v
  refine ⟨a, ?_, ha_eq⟩
  -- Need: evaln t₂ code input_nat = some a
  -- i.e., a ∈ evaln t₂ code input_nat
  -- We have a ∈ evaln t₁ code input_nat and t₁ ≤ t₂
  exact Nat.Partrec.Code.evaln_mono hle ha_mem

-- ════════════════════════════════════════════════════════════
-- Section 5: Bundle as StepBoundedTM
-- ════════════════════════════════════════════════════════════

/-- A concrete StepBoundedTM built on Mathlib's partial recursive codes. -/
def classical_tm : StepBoundedTM where
  run      := concreteRun
  run_zero := concreteRun_zero
  run_mono := concreteRun_mono

-- ════════════════════════════════════════════════════════════
-- Section 6: Axiom audit
-- ════════════════════════════════════════════════════════════

-- Audit trail: the only non-Lean axioms in classical_tm are the standard
-- Lean/Mathlib foundations (propext, Classical.choice, Quot.sound).
#print axioms classical_tm

end ClassicalBridge.TM
