/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Mirror/CountingFunctions.lean — Mirror of counting function
definitions from pnp-integrated/PNP/CoreInfrastructure.lean and key theorems
from pnp-integrated/PNP/AntiCompression/PolynomialAntiCompression.lean for
cross-repo compilation.

These definitions are exact copies of the originals. The mirroring pattern
is the same as GRM.lean and AdmissibleEncoding.lean: the types are restated
here so this repo can be compiled independently without importing the
pnp-integrated build artifact.

## Proved here (with Mathlib available)

- N_Val_pos, N_Val_ge_2, N_Val_mono, N_Val_mono_succ
- meso_has_growth_gap (growth gap at constant overhead)

## Also proved here

- growth_gap_survives_poly: the growth gap survives polynomial overhead
  (ported from PNP.AntiCompression.PolynomialAntiCompression)
  Helper lemmas: two_pow_succ_gt, two_pow_strict_mono, two_pow_mono,
  two_pow_gt_n, two_pow_ge_sq, pow_self_ge_two_pow, exp_dominates_poly_sum

STATUS: 0 sorry. 0 axioms.
-/

import ClassicalBridge.Mirror.GRM
import Mathlib.Algebra.Order.Ring.Nat

namespace ClassicalBridge

-- ════════════════════════════════════════════════════════════
-- Mirrored from PNP/CoreInfrastructure.lean: Growth gap
-- ════════════════════════════════════════════════════════════

/-- Growth gap predicate: endomorphism counts eventually exceed carrier
    counts even after shifting by overhead. -/
def HasGrowthGap (N_End N_L : Nat → Nat) (overhead : Nat) : Prop :=
  ∃ g, N_End g > N_L (g + overhead)

-- ════════════════════════════════════════════════════════════
-- Mirrored from PNP/CoreInfrastructure.lean: Polynomial bounds
-- ════════════════════════════════════════════════════════════

/-- A polynomial bound with degree and constant term. -/
structure PolyBound where
  degree : Nat
  constant : Nat

/-- Evaluate a polynomial bound: p(n) = n^degree + constant. -/
def PolyBound.eval (p : PolyBound) (n : Nat) : Nat :=
  n ^ p.degree + p.constant

-- ════════════════════════════════════════════════════════════
-- Mirrored from PNP/CoreInfrastructure.lean: Counting functions
-- ════════════════════════════════════════════════════════════

/-- Number of distinct values with binary description length <= g. -/
def N_Val (g : Nat) : Nat := 2 ^ (g + 1)

/-- Number of distinct endomorphisms on g-bit values. -/
def N_End (g : Nat) : Nat := N_Val g ^ N_Val g

-- ════════════════════════════════════════════════════════════
-- Proved theorems (arithmetic, provable with Mathlib)
-- ════════════════════════════════════════════════════════════

/-- N_Val is positive: 2^(g+1) > 0. -/
theorem N_Val_pos (g : Nat) : N_Val g > 0 := by
  unfold N_Val
  exact Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.one_le_two_pow))

/-- N_Val is at least 2 for all g. -/
theorem N_Val_ge_2 (g : Nat) : N_Val g ≥ 2 := by
  unfold N_Val
  calc 2 ^ (g + 1) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 2 := by omega

/-- N_Val is monotone (general form). -/
theorem N_Val_mono {g₁ g₂ : Nat} (h : g₁ ≤ g₂) : N_Val g₁ ≤ N_Val g₂ := by
  unfold N_Val
  exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)

/-- N_Val is monotone (successor form). -/
theorem N_Val_mono_succ (g : Nat) : N_Val g ≤ N_Val (g + 1) :=
  N_Val_mono (Nat.le_succ g)

/-- Growth gap at constant overhead: for any constant c, there exists g
    such that N_End(g) > N_Val(g + c).

    Proof: take g = c. Then N_End(c) = (2^(c+1))^(2^(c+1)) and
    N_Val(c+c) = 2^(2c+1). Since 2^(c+1) ≥ 2, we have
    (2^(c+1))^(2^(c+1)) ≥ (2^(c+1))^2 = 2^(2c+2) > 2^(2c+1). -/
theorem meso_has_growth_gap (c : Nat) : HasGrowthGap N_End N_Val c := by
  refine ⟨c, ?_⟩
  show (2 ^ (c + 1)) ^ (2 ^ (c + 1)) > 2 ^ (c + c + 1)
  have h_base_ge : 2 ^ (c + 1) ≥ 2 := N_Val_ge_2 c
  -- (2^(c+1))^(2^(c+1)) ≥ (2^(c+1))^2 since 2^(c+1) ≥ 2
  have h_self_ge_sq : (2 ^ (c + 1)) ^ (2 ^ (c + 1)) ≥ (2 ^ (c + 1)) ^ 2 :=
    Nat.pow_le_pow_right (by omega : 0 < 2 ^ (c + 1)) h_base_ge
  -- (2^(c+1))^2 = 2^(2*(c+1)) = 2^(2c+2)
  have h_pow_sq : (2 ^ (c + 1)) ^ 2 = 2 ^ ((c + 1) * 2) := by
    rw [← Nat.pow_mul]
  -- 2c+2 > 2c+1 = c+c+1
  have h_exp_gt : (c + 1) * 2 > c + c + 1 := by omega
  -- 2^(2c+2) > 2^(2c+1)
  have h_strict : 2 ^ ((c + 1) * 2) > 2 ^ (c + c + 1) :=
    Nat.pow_lt_pow_right (by omega : 1 < 2) h_exp_gt
  omega

-- ════════════════════════════════════════════════════════════
-- Mirrored from PNP/CoreInfrastructure.lean: GradeStructure
-- ════════════════════════════════════════════════════════════

/-- Abstract grade structure on an endomorphism algebra and carrier. -/
structure GradeStructure where
  /-- Cumulative count of endomorphisms with grade <= g. -/
  N_End : Nat → Nat
  /-- Cumulative count of carrier elements with grade <= g. -/
  N_L : Nat → Nat
  /-- Monotonicity: cumulative counts are non-decreasing. -/
  N_End_mono : ∀ g, N_End g ≤ N_End (g + 1)
  N_L_mono : ∀ g, N_L g ≤ N_L (g + 1)

-- ════════════════════════════════════════════════════════════
-- Helper arithmetic lemmas (ported from PNP.CoreArithmetic)
-- ════════════════════════════════════════════════════════════

/-- 2^(n+1) > 2^n. -/
private theorem two_pow_succ_gt (n : Nat) : 2 ^ (n + 1) > 2 ^ n := by
  have : 2 ^ n ≥ 1 := Nat.one_le_pow n 2 (by omega)
  rw [Nat.pow_succ]; omega

/-- 2^m < 2^n when m < n. -/
private theorem two_pow_strict_mono {m n : Nat} (h : m < n) : 2 ^ m < 2 ^ n := by
  induction h with
  | refl => exact two_pow_succ_gt m
  | step _ ih => exact Nat.lt_trans ih (two_pow_succ_gt _)

/-- 2^m ≤ 2^n when m ≤ n. -/
private theorem two_pow_mono {m n : Nat} (h : m ≤ n) : 2 ^ m ≤ 2 ^ n :=
  Nat.pow_le_pow_right (by omega : 0 < 2) h

/-- 2^n > n for all n. -/
private theorem two_pow_gt_n : ∀ n, 2 ^ n > n := by
  intro n
  induction n with
  | zero => decide
  | succ k ih =>
    have : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    have : 2 ^ k ≥ 1 := Nat.one_le_two_pow
    omega

/-- 2^m ≥ m * m for m ≥ 4. -/
private theorem two_pow_ge_sq (m : Nat) (hm : m ≥ 4) : 2 ^ m ≥ m * m := by
  induction m with
  | zero => omega
  | succ k ih =>
    match Nat.lt_or_ge k 4 with
    | Or.inl hk =>
      have : k = 3 := by omega
      subst this; decide
    | Or.inr hk =>
      have ihk := ih hk
      have h_pow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
      have h_expand : (k + 1) * (k + 1) = k * k + k + k + 1 := by
        rw [Nat.succ_mul, Nat.mul_succ]; omega
      rw [h_pow, h_expand]
      have h1 : 2 ^ k * 2 ≥ k * k * 2 := Nat.mul_le_mul_right 2 ihk
      have h_kk : k * k ≥ 4 * k := Nat.mul_le_mul_right k hk
      omega

/-- For a ≥ 2, a^a ≥ 2^a. -/
private theorem pow_self_ge_two_pow (a : Nat) (ha : a ≥ 2) : a ^ a ≥ 2 ^ a :=
  Nat.pow_le_pow_left ha a

-- ════════════════════════════════════════════════════════════
-- Key arithmetic: exponential dominates polynomial
-- ════════════════════════════════════════════════════════════

/-- For any d c, there exists g such that 2^(g+1) > g + g^d + c + 1.
    Ported from PNP.AntiCompression.PolynomialAntiCompression.exp_dominates_poly_sum.
    Witness: g = 2^(d + c + 4). -/
private theorem exp_dominates_poly_sum (d c : Nat) :
    ∃ g, 2 ^ (g + 1) > g + g ^ d + c + 1 := by
  let m := d + c + 4
  refine ⟨2 ^ m, ?_⟩
  have hm_ge : m ≥ 4 := by omega
  have hd_le : d ≤ m - 4 := by omega
  have h_gd : (2 ^ m) ^ d = 2 ^ (m * d) := by rw [← Nat.pow_mul]
  have h_md_lt : m * d < 2 ^ m := by
    have h1 : m * d ≤ m * (m - 4) := Nat.mul_le_mul_left m hd_le
    have h2 : m * (m - 4) < m * m :=
      Nat.mul_lt_mul_of_pos_left (by omega : m - 4 < m) (by omega : m > 0)
    have h3 : m * m ≤ 2 ^ m := two_pow_ge_sq m hm_ge
    omega
  have h_tower_gt_md : 2 ^ (2 ^ m) > 2 ^ (m * d) := two_pow_strict_mono h_md_lt
  have h_tower_gt_m : 2 ^ (2 ^ m) > 2 ^ m := two_pow_strict_mono (two_pow_gt_n m)
  have h_c_lt : c + 1 < 2 ^ m := by
    calc c + 1 < c + 4 := by omega
      _ ≤ m := by omega
      _ < 2 ^ m := two_pow_gt_n m
  have h_double : 2 ^ (2 ^ m + 1) = 2 * 2 ^ (2 ^ m) := by
    have : 2 ^ (2 ^ m + 1) = 2 ^ (2 ^ m) * 2 := Nat.pow_succ 2 (2 ^ m)
    omega
  rw [h_double, h_gd]
  have h_second_half : 2 ^ (2 ^ m) > 2 ^ m + (c + 1) := by
    have h_ge_2m : 2 ^ (2 ^ m) ≥ 2 * 2 ^ m := by
      have h1 : 2 ^ (2 ^ m) ≥ 2 ^ (m + 1) := two_pow_mono (two_pow_gt_n m)
      have h2 : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
      omega
    omega
  omega

-- ════════════════════════════════════════════════════════════
-- Proved theorem (ported from pnp-integrated)
-- ════════════════════════════════════════════════════════════

/-- The growth gap survives polynomial overhead.

    For any polynomial bound p(g) = g^d + c, there exists a grade g where
    N_End(g) > N_Val(g + p(g)).

    Ported from PNP.AntiCompression.PolynomialAntiCompression.growth_gap_survives_poly.

    Proof: exp_dominates_poly_sum gives g with 2^(g+1) > g + g^d + c + 1.
    Then N_End(g) = (2^(g+1))^(2^(g+1)) ≥ 2^(2^(g+1)) (since base ≥ 2)
    and N_Val(g + p(g)) = 2^(g + g^d + c + 1) < 2^(2^(g+1)) by monotonicity. -/
theorem growth_gap_survives_poly (p : PolyBound) :
    ∃ g, N_End g > N_Val (g + p.eval g) := by
  obtain ⟨g, hg⟩ := exp_dominates_poly_sum p.degree p.constant
  refine ⟨g, ?_⟩
  unfold N_End N_Val PolyBound.eval
  show (2 ^ (g + 1)) ^ (2 ^ (g + 1)) > 2 ^ (g + (g ^ p.degree + p.constant) + 1)
  have h_base_ge : 2 ^ (g + 1) ≥ 2 := N_Val_ge_2 g
  have h_tower : (2 ^ (g + 1)) ^ (2 ^ (g + 1)) ≥ 2 ^ (2 ^ (g + 1)) :=
    pow_self_ge_two_pow (2 ^ (g + 1)) h_base_ge
  have h_hg' : g + (g ^ p.degree + p.constant) + 1 < 2 ^ (g + 1) := by omega
  have h_exp_mono : 2 ^ (2 ^ (g + 1)) > 2 ^ (g + (g ^ p.degree + p.constant) + 1) :=
    two_pow_strict_mono h_hg'
  omega

end ClassicalBridge
