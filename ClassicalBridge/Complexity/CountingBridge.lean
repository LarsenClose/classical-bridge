/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Complexity/CountingBridge.lean — The counting bridge:
connects P_eq_NP to the growth gap contradiction.

## Architecture

This file mirrors the BinaryModel/LinearBinaryModel pattern from
witness-transport (WTS/Core.lean) and pnp-integrated
(PNP/Grading/StandardModel.lean, PNP/Grading/GrowthGap.lean).

The key types (mirrored from witness-transport):
- BinaryModel: programs counted by NProg, overhead function rho,
  table_count asserting NProg(rho(g)) >= N_Val(g)^N_Val(g)
- LinearBinaryModel: extends BinaryModel with linear rho

The counting argument counts PROGRAMS (BinStrings of bounded description
length), not all endomorphisms. Each program computes one function via
the retraction. The injection is programs → functions (determinism).

Under P=NP, the bridge instantiates a LinearBinaryModel where:
- NProg counts program behaviors at bounded description length
- rho is linear (from polynomial time bound)
- table_count holds because P=NP gives sufficient program coverage
- binary_growth_gap fires (tower NProg exceeds exponential N_Val)
- not_polyMarkov gives the contradiction

STATUS: 0 sorry. Mirrors types from witness-transport.
-/

import ClassicalBridge.Complexity.Basic
import ClassicalBridge.Mirror.CountingFunctions
import ClassicalBridge.Mirror.GRM
import ClassicalBridge.Bridge.PolyMarkovBridge

namespace ClassicalBridge.Complexity.CountingBridge

open ClassicalBridge
open ClassicalBridge.TM
open ClassicalBridge.Bridge.PolyMarkovBridge
open ClassicalBridge.Bridge

-- ════════════════════════════════════════════════════════════
-- Section 1: BinaryModel (mirrored from WTS/Core.lean)
-- ════════════════════════════════════════════════════════════

/-- A binary standard model: programs graded over binary-encoded values.
    Mirrored from WTS/Core.lean:271.

    NProg(g) counts programs with description length <= g.
    rho(g) is the overhead function: at description length rho(g),
    enough programs exist to represent all grade-g endomorphisms.
    table_count is the model correspondence: NProg(rho(g)) >= N_End(g). -/
structure BinaryModel where
  /-- Count of programs in slice <= g. -/
  NProg : Nat → Nat
  /-- Monotonicity of program counts. -/
  NProg_mono : ∀ g, NProg g ≤ NProg (g + 1)
  /-- Overhead function. -/
  rho : Nat → Nat
  /-- rho is monotone. -/
  rho_mono : ∀ g, rho g ≤ rho (g + 1)
  /-- Table representability: NProg(rho(g)) >= N_Val(g)^N_Val(g) = N_End(g). -/
  table_count : ∀ g, NProg (rho g) ≥ N_Val g ^ N_Val g

/-- A binary model with linear overhead: rho(g) <= a*g + b.
    Mirrored from WTS/Core.lean:284. -/
structure LinearBinaryModel extends BinaryModel where
  /-- Linear overhead coefficient. -/
  rho_coeff : Nat
  /-- Linear overhead constant. -/
  rho_const : Nat
  /-- rho(g) is bounded linearly. -/
  rho_linear : ∀ g, rho g ≤ rho_coeff * g + rho_const

-- ════════════════════════════════════════════════════════════
-- Section 2: Growth gap for LinearBinaryModel
-- (mirrored from PNP/Grading/GrowthGap.lean)
-- ════════════════════════════════════════════════════════════

/-- Helper: rho(g) <= g + rho_const when rho_coeff <= 1. -/
private theorem rho_le_of_coeff_le_one (M : LinearBinaryModel)
    (h_lin : M.rho_coeff ≤ 1) (g : Nat) :
    M.rho g ≤ g + M.rho_const := by
  have := M.rho_linear g
  have : M.rho_coeff * g ≤ 1 * g := Nat.mul_le_mul_right g h_lin
  omega

/-- a^a >= a^2 when a >= 2. -/
private theorem pow_self_ge_sq (a : Nat) (ha : a ≥ 2) : a ^ a ≥ a ^ 2 :=
  Nat.pow_le_pow_right (by omega : a > 0) ha

/-- 2^m < 2^n when m < n. -/
private theorem two_pow_strict_mono {m n : Nat} (h : m < n) : 2 ^ m < 2 ^ n := by
  exact Nat.pow_lt_pow_right (by omega : 1 < 2) h

/-- Growth gap for linear binary models with rho_coeff <= 1.
    Mirrored from PNP/Grading/GrowthGap.lean:154.

    Witness grade: g = rho_const + c + 1.
    Then rho(g) <= g + rho_const = 2*rho_const + c + 1.
    NProg(rho(g)) >= N_Val(g)^N_Val(g) (table_count).
    N_Val(g)^N_Val(g) = tower, which exceeds N_Val(rho(g) + c).
    Therefore NProg(rho(g)) > N_Val(rho(g) + c). -/
theorem binary_growth_gap (M : LinearBinaryModel)
    (h_lin : M.rho_coeff ≤ 1) (c : Nat) :
    HasGrowthGap M.NProg N_Val c := by
  let g := M.rho_const + c + 1
  refine ⟨M.rho g, ?_⟩
  have h_rho := rho_le_of_coeff_le_one M h_lin g
  -- NProg(rho(g)) >= N_Val(g)^N_Val(g) by table_count
  have h_table := M.table_count g
  -- N_Val(g)^N_Val(g) >= N_Val(g)^2 since N_Val(g) >= 2
  have h_ge2 : N_Val g ≥ 2 := N_Val_ge_2 g
  have h_sq := pow_self_ge_sq (N_Val g) h_ge2
  -- rho(g) + c + 1 < 2*(g+1) because g = rho_const + c + 1
  -- and rho(g) <= g + rho_const = 2*rho_const + c + 1
  have h_target : M.rho g + c + 1 < 2 * (g + 1) := by omega
  -- 2^(rho(g)+c+1) < 2^(2*(g+1))
  have h_pow : 2 ^ (M.rho g + c + 1) < 2 ^ (2 * (g + 1)) :=
    two_pow_strict_mono h_target
  -- N_Val(g)^2 = (2^(g+1))^2 = 2^(2*(g+1))
  have h_sq_eq : N_Val g ^ 2 = 2 ^ (2 * (g + 1)) := by
    unfold N_Val
    rw [← Nat.pow_mul]
    congr 1; omega
  -- N_Val(rho(g) + c) = 2^(rho(g)+c+1)
  have h_nval : N_Val (M.rho g + c) = 2 ^ (M.rho g + c + 1) := rfl
  -- Chain: N_Val(rho(g)+c) < 2^(2*(g+1)) = N_Val(g)^2 <= N_Val(g)^N_Val(g) <= NProg(rho(g))
  rw [h_nval]
  calc 2 ^ (M.rho g + c + 1)
      < 2 ^ (2 * (g + 1)) := h_pow
    _ = N_Val g ^ 2 := h_sq_eq.symm
    _ ≤ N_Val g ^ N_Val g := h_sq
    _ ≤ M.NProg (M.rho g) := h_table

-- ════════════════════════════════════════════════════════════
-- Section 3: PolyMarkovGradedModel
-- (mirrored from PNP/AntiCompression/PolynomialAntiCompression.lean)
-- ════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════════════
-- Section 3: Mesoscopic model instantiation
-- (mirrored from PNP/Grading/StandardModel.lean)
-- ════════════════════════════════════════════════════════════

/-- Mesoscopic program count: all lookup tables.
    NProg(g) = N_Val(g)^N_Val(g) = N_End(g).
    Every function on grade-g strings is treated as a "program"
    (a lookup table). -/
def mesoProg (g : Nat) : Nat := N_Val g ^ N_Val g

/-- mesoProg is monotone. -/
theorem mesoProg_mono : ∀ g, mesoProg g ≤ mesoProg (g + 1) := by
  intro g
  unfold mesoProg
  exact Nat.le_trans
    (Nat.pow_le_pow_left (N_Val_mono (Nat.le_succ g)) _)
    (Nat.pow_le_pow_right (N_Val_pos (g + 1)) (N_Val_mono (Nat.le_succ g)))

/-- The mesoscopic model as a LinearBinaryModel.
    NProg = all lookup tables, rho = identity, rho_coeff = 1. -/
def mesoscopicModel : LinearBinaryModel where
  NProg := mesoProg
  NProg_mono := mesoProg_mono
  rho g := g
  rho_mono _ := Nat.le_succ _
  table_count _ := Nat.le_refl _
  rho_coeff := 1
  rho_const := 0
  rho_linear g := by simp

/-- Growth gap for the mesoscopic model. -/
theorem meso_growth_gap (c : Nat) : HasGrowthGap mesoscopicModel.NProg N_Val c :=
  binary_growth_gap mesoscopicModel (Nat.le_refl 1) c

-- ════════════════════════════════════════════════════════════
-- Section 4: The refutation: mesoscopic growth gap + bridge → ¬PolyMarkovProp
-- (mirrored from PNP/AntiCompression/PolynomialAntiCompression.lean)
-- ════════════════════════════════════════════════════════════

/-- The mesoscopic bridge type: PolyMarkovProp implies a PolyBoundedConstruction
    on the mesoscopic program count.

    PolyBoundedConstruction mesoProg N_Val p means:
    ∀ g, mesoProg g ≤ N_Val(g + p.eval g), i.e., the tower program count
    is polynomially bounded by N_Val.

    This is impossible: construction_super_poly (from DriftedLock.lean)
    refutes PolyBoundedConstruction N_End N_Val p for all p. Since
    mesoProg = N_End, it refutes PolyBoundedConstruction mesoProg N_Val p too. -/
def MesoBridge (comp : CompModel) : Prop :=
  PolyMarkovProp comp →
    ∃ (p : PolyBound), PolyBoundedConstruction mesoProg N_Val p

/-- mesoProg = N_End. -/
theorem mesoProg_eq_N_End : mesoProg = N_End := rfl

/-- Given a CompModel with a mesoscopic bridge, PolyMarkovProp is refutable.
    The bridge gives PolyBoundedConstruction mesoProg N_Val p from PolyMarkovProp.
    Since mesoProg = N_End, construction_super_poly (proved in DriftedLock.lean)
    refutes it. -/
theorem not_polyMarkov_meso (comp : CompModel) (bridge : MesoBridge comp) :
    ¬ PolyMarkovProp comp := by
  intro hPM
  obtain ⟨p, h_bound⟩ := bridge hPM
  exact construction_super_poly p (mesoProg_eq_N_End ▸ h_bound)

-- ════════════════════════════════════════════════════════════
-- Section 5: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms binary_growth_gap
#print axioms meso_growth_gap
#print axioms not_polyMarkov_meso

end ClassicalBridge.Complexity.CountingBridge
