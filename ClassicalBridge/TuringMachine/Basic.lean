/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/TuringMachine/Basic.lean — Minimal Turing machine model
for the classical bridge.

DESIGN CHOICE: We use a streamlined step-bounded TM rather than importing
Mathlib's full TM2 hierarchy. The goal is the minimum classical model
needed to instantiate AdmissibleEncoding, not a general-purpose TM library.

The carrier type is binary strings (List Bool). The grade is string length.
fold/unfold come from a universal TM self-interpretation pair.

STATUS: Complete. 0 sorry.
-/

import Mathlib.Data.List.Basic

namespace ClassicalBridge.TM

-- ════════════════════════════════════════════════════════════
-- Section 1: Binary strings as the carrier
-- ════════════════════════════════════════════════════════════

/-- Binary strings. The carrier type for classical computation. -/
abbrev BinString := List Bool

/-- Grade = description length = string length. -/
def grade (s : BinString) : Nat := s.length

theorem grade_nil : grade [] = 0 := rfl

theorem grade_cons (b : Bool) (s : BinString) : grade (b :: s) = grade s + 1 := by
  simp [grade, List.length_cons]

theorem grade_append (s₁ s₂ : BinString) : grade (s₁ ++ s₂) = grade s₁ + grade s₂ := by
  simp [grade, List.length_append]

-- ════════════════════════════════════════════════════════════
-- Section 2: Step-bounded computation
-- ════════════════════════════════════════════════════════════

/-- A deterministic step-bounded computation model on binary strings.
    Programs are binary strings (Goedel numbering).

    This is an abstract interface: we axiomatize the behavior of a
    deterministic TM rather than building the full state-machine
    internals. This is sufficient for the bridge because we only
    need the input/output behavior and step-monotonicity, not the
    internal state transitions. -/
structure StepBoundedTM where
  /-- Run program p on input x for at most t steps.
      Returns `some v` if the computation halts with output v
      within t steps, or `none` if it hasn't halted yet. -/
  run : BinString → BinString → Nat → Option BinString
  /-- Zero steps never produce output. -/
  run_zero : ∀ p x, run p x 0 = none
  /-- Monotonicity: once a computation halts, more steps don't change
      the result. This is the fundamental property of deterministic
      computation: halting is a permanent state. -/
  run_mono : ∀ p x t₁ t₂ v, run p x t₁ = some v → t₁ ≤ t₂ → run p x t₂ = some v

/-- A program p computes function f if for every input x, there exists
    a step count at which p halts with output f(x). -/
def StepBoundedTM.Computes (M : StepBoundedTM) (p : BinString) (f : BinString → BinString) : Prop :=
  ∀ x, ∃ t, M.run p x t = some (f x)

/-- A program p halts on input x if there exists some step count
    at which it produces output. -/
def StepBoundedTM.Halts (M : StepBoundedTM) (p : BinString) (x : BinString) : Prop :=
  ∃ t v, M.run p x t = some v

/-- A program p computes function f within time bound T if for every
    input x, the computation halts within T(|p|, |x|) steps. -/
def StepBoundedTM.ComputesInTime (M : StepBoundedTM) (p : BinString) (f : BinString → BinString)
    (T : Nat → Nat → Nat) : Prop :=
  ∀ x, M.run p x (T (grade p) (grade x)) = some (f x)

-- ════════════════════════════════════════════════════════════
-- Section 3: Determinacy
-- ════════════════════════════════════════════════════════════

/-- If a step-bounded TM halts at two different step counts, it
    produces the same output. This follows from monotonicity. -/
theorem StepBoundedTM.run_deterministic (M : StepBoundedTM)
    (p x : BinString) (t₁ t₂ : Nat) (v₁ v₂ : BinString)
    (h₁ : M.run p x t₁ = some v₁) (h₂ : M.run p x t₂ = some v₂) :
    v₁ = v₂ := by
  rcases Nat.le_total t₁ t₂ with h | h
  · have := M.run_mono p x t₁ t₂ v₁ h₁ h
    rw [this] at h₂
    exact Option.some.inj h₂
  · have := M.run_mono p x t₂ t₁ v₂ h₂ h
    rw [this] at h₁
    exact (Option.some.inj h₁).symm

-- ════════════════════════════════════════════════════════════
-- Section 4: Pairing for complexity class definitions
-- ════════════════════════════════════════════════════════════

/-- Pair two binary strings using a unary length prefix.
    pair a b = [false, ..., false, true] ++ a ++ b
    where the prefix has |a| false bits followed by one true bit.
    This is self-delimiting: |a| can be recovered by counting
    leading false bits. Used by NPVerifier in Complexity/Basic.lean. -/
def pair (a b : BinString) : BinString :=
  List.replicate a.length false ++ [true] ++ a ++ b

/-- Grade of a paired string. -/
theorem grade_pair (a b : BinString) :
    grade (pair a b) = a.length + 1 + a.length + b.length := by
  simp [pair, grade, List.length_append, List.length_replicate]
  omega

end ClassicalBridge.TM
