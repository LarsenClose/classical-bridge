/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Encoding/GradeStructure.lean — Grade structure on
binary string encodings: description length as the natural grade.

The grade function grade(s) = s.length satisfies the key properties:
- Non-negative (trivially: it is a Nat)
- Additive under concatenation: grade(a ++ b) = grade(a) + grade(b)
- Monotone under prefix/sublist extraction
- Composable: if f adds c₁ overhead and g adds c₂, then f ∘ g adds c₁ + c₂

Additionally defines a GradeBound structure that packages overhead bounds
for compositions, and states the polynomial output-size bound for
polynomial-time computable functions.

STATUS: 0 sorry.
-/

import ClassicalBridge.TuringMachine.Basic
import ClassicalBridge.Encoding.BinaryEncoding

namespace ClassicalBridge.Encoding

open ClassicalBridge.TM

-- ════════════════════════════════════════════════════════════
-- Section 1: Basic grade properties
-- ════════════════════════════════════════════════════════════

/-- Grade is non-negative. (Trivial since grade : BinString → Nat.) -/
theorem grade_nonneg (s : BinString) : 0 ≤ grade s :=
  Nat.zero_le _

/-- Grade of the empty string is zero. -/
theorem grade_empty : grade ([] : BinString) = 0 := rfl

/-- Grade is additive under concatenation. -/
theorem grade_append (s₁ s₂ : BinString) : grade (s₁ ++ s₂) = grade s₁ + grade s₂ :=
  TM.grade_append s₁ s₂

/-- Grade is monotone under prefix extraction (List.take). -/
theorem grade_take_le (s : BinString) (n : Nat) : grade (s.take n) ≤ grade s := by
  simp [grade, List.length_take]
  exact Nat.min_le_right n s.length

/-- Grade is monotone under suffix extraction (List.drop). -/
theorem grade_drop_le (s : BinString) (n : Nat) : grade (s.drop n) ≤ grade s := by
  simp [grade]

/-- Prefix has grade at most n. -/
theorem grade_take_le_n (s : BinString) (n : Nat) : grade (s.take n) ≤ n := by
  simp [grade, List.length_take]
  exact Nat.min_le_left n s.length

-- ════════════════════════════════════════════════════════════
-- Section 2: Grade bounds and composition
-- ════════════════════════════════════════════════════════════

/-- A grade bound packages a function and its additive overhead guarantee.
    If f has overhead c, then for all x: grade(f(x)) ≤ grade(x) + c.
    This is the structure needed for AdmissibleEncoding.selfApp_bounded. -/
structure GradeBound where
  /-- The function on binary strings. -/
  fn : BinString → BinString
  /-- The additive overhead constant. -/
  overhead : Nat
  /-- The grade bound guarantee. -/
  bound : ∀ (x : BinString), grade (fn x) ≤ grade x + overhead

/-- The identity function has overhead 0. -/
def GradeBound.id : GradeBound where
  fn := _root_.id
  overhead := 0
  bound := by simp [grade]

/-- Composition of grade-bounded functions: overheads add. -/
def GradeBound.comp (f g : GradeBound) : GradeBound where
  fn := f.fn ∘ g.fn
  overhead := f.overhead + g.overhead
  bound := by
    intro x
    simp only [Function.comp]
    have h1 := f.bound (g.fn x)
    have h2 := g.bound x
    omega

/-- Composing n copies of a grade-bounded function multiplies the overhead. -/
def GradeBound.iterate (f : GradeBound) : Nat → GradeBound
  | 0 => GradeBound.id
  | n + 1 => GradeBound.comp f (f.iterate n)

theorem GradeBound.iterate_overhead (f : GradeBound) (n : Nat) :
    (f.iterate n).overhead = n * f.overhead := by
  induction n with
  | zero => simp [iterate, GradeBound.id]
  | succ n ih =>
    simp only [iterate, comp, ih]
    rw [Nat.succ_mul]
    omega

/-- If f has additive overhead c₁ and g has additive overhead c₂,
    then f ∘ g has additive overhead c₁ + c₂. -/
theorem grade_comp_le (f g : BinString → BinString) (c₁ c₂ : Nat)
    (hf : ∀ x, grade (f x) ≤ grade x + c₁)
    (hg : ∀ x, grade (g x) ≤ grade x + c₂) :
    ∀ x, grade (f (g x)) ≤ grade x + (c₁ + c₂) := by
  intro x
  calc grade (f (g x))
      ≤ grade (g x) + c₁ := hf (g x)
    _ ≤ (grade x + c₂) + c₁ := Nat.add_le_add_right (hg x) c₁
    _ = grade x + (c₁ + c₂) := by omega

-- ════════════════════════════════════════════════════════════
-- Section 3: Multiplicative grade bounds
-- ════════════════════════════════════════════════════════════

/-- A multiplicative grade bound: grade(f(x)) ≤ c * grade(x) + d.
    This captures the behavior of polynomial-time functions on the
    output length: a TM running in time p(n) can write at most p(n)
    symbols, so |f(x)| ≤ p(|x|). For linear-time functions this gives
    a multiplicative bound. -/
structure MultGradeBound where
  /-- The function on binary strings. -/
  fn : BinString → BinString
  /-- Multiplicative factor. -/
  mult : Nat
  /-- Additive constant. -/
  add : Nat
  /-- The bound. -/
  bound : ∀ (x : BinString), grade (fn x) ≤ mult * grade x + add

/-- Every additive GradeBound is a MultGradeBound with mult=1. -/
def GradeBound.toMult (f : GradeBound) : MultGradeBound where
  fn := f.fn
  mult := 1
  add := f.overhead
  bound := by
    intro x
    simp
    exact f.bound x

/-- Composition of multiplicative grade bounds. -/
def MultGradeBound.comp (f g : MultGradeBound) : MultGradeBound where
  fn := f.fn ∘ g.fn
  mult := f.mult * g.mult
  add := f.mult * g.add + f.add
  bound := by
    intro x
    simp only [Function.comp]
    calc grade (f.fn (g.fn x))
        ≤ f.mult * grade (g.fn x) + f.add := f.bound (g.fn x)
      _ ≤ f.mult * (g.mult * grade x + g.add) + f.add := by
          apply Nat.add_le_add_right
          apply Nat.mul_le_mul_left
          exact g.bound x
      _ = f.mult * g.mult * grade x + (f.mult * g.add + f.add) := by
          rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

-- ════════════════════════════════════════════════════════════
-- Section 4: Polynomial output-size bound (axiomatized)
-- ════════════════════════════════════════════════════════════

/-- AXIOM (Classical TM theory): A Turing machine running for t steps
    can write at most t symbols to its output tape. Therefore, if a
    function f is computable in time T(n) on inputs of length n,
    then |f(x)| ≤ T(|x|) for all x.

    CLASSICAL JUSTIFICATION: In one step, a TM can write at most one
    symbol. After t steps it has written at most t symbols. This is a
    basic property of the TM model, not dependent on any complexity
    assumption. The full proof would require formalizing TM execution
    traces and counting write operations, which is orthogonal to the
    bridge construction. -/
axiom polytime_output_bound (M : StepBoundedTM) (p : BinString)
    (f : BinString → BinString) (T : Nat → Nat → Nat)
    (hcomp : M.ComputesInTime p f T) :
    ∀ (x : BinString), grade (f x) ≤ T (grade p) (grade x)

/-- Corollary: if f is computable in polynomial time p(n),
    then f is a MultGradeBound with parameters derived from p.

    Specifically, for a polynomial T(k, n) ≤ c * n^d + e where k = |p|
    is fixed, we get a multiplicative bound on the output grade. This
    is sufficient to show that polynomial-time reductions between encodings
    preserve the grade structure needed for AdmissibleEncoding/SameSemantics. -/
theorem polytime_gives_mult_bound (M : StepBoundedTM) (p : BinString)
    (f : BinString → BinString) (c d : Nat)
    (T : Nat → Nat → Nat)
    (hcomp : M.ComputesInTime p f T)
    (hpoly : ∀ (x : BinString), T (grade p) (grade x) ≤ c * (grade x) ^ d + c) :
    ∀ (x : BinString), grade (f x) ≤ c * (grade x) ^ d + c := by
  intro x
  calc grade (f x) ≤ T (grade p) (grade x) := polytime_output_bound M p f T hcomp x
    _ ≤ c * (grade x) ^ d + c := hpoly x

end ClassicalBridge.Encoding
