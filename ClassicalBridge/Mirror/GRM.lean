/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Mirror/GRM.lean — Mirror of core GRM definitions from
witness-transport/WTS/Core.lean for cross-repo compilation.

These definitions are exact copies of the originals. The mirroring pattern
is the same as SideAMirror.lean in witness-transport: the types are
restated here so this repo can be compiled independently without importing
the witness-transport build artifact.

STATUS: 0 sorry.
-/

namespace ClassicalBridge

-- ════════════════════════════════════════════════════════════
-- Mirrored from WTS/Core.lean
-- ════════════════════════════════════════════════════════════

structure GradedReflModel where
  carrier : Type
  fold : carrier → carrier
  unfold : carrier → carrier
  roundtrip : ∀ x, fold (unfold x) = x
  grade : carrier → Nat

def GradedReflModel.selfApp (M : GradedReflModel) (x : M.carrier) : M.carrier :=
  M.unfold (M.fold x)

def FactorsThrough (M : GradedReflModel) (f : M.carrier → M.carrier) (d : Nat) : Prop :=
  ∀ x, M.grade x ≤ d → M.grade (f x) ≤ d

structure SelfAppUnbounded (M : GradedReflModel) where
  overflows : ∀ d, ∃ x, M.grade x ≤ d ∧ M.grade (M.selfApp x) > d

def PEqNP (M : GradedReflModel) : Prop :=
  ∃ d, FactorsThrough M M.selfApp d

-- ════════════════════════════════════════════════════════════
-- Mirrored from WTS/Tower/CarrierEngineering/ReencodingInvariance.lean
-- ════════════════════════════════════════════════════════════

structure BoundedGRMEquiv (M M' : GradedReflModel) where
  f : M.carrier → M'.carrier
  g : M'.carrier → M.carrier
  gf : ∀ x, g (f x) = x
  fg : ∀ x', f (g x') = x'
  overhead : Nat
  f_bounded : ∀ x, M'.grade (f x) ≤ M.grade x + overhead
  g_bounded : ∀ x', M.grade (g x') ≤ M'.grade x' + overhead
  f_compat : ∀ x, M'.selfApp (f x) = f (M.selfApp x)

end ClassicalBridge
