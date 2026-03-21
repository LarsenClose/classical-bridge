/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Complexity/ModelCorrespondence.lean — The model correspondence.

Parameterized regime classification: given a model-semantics pairing,
produces the regime-specific result. The output toggles depending on
the parameters:

- DriftedPairing (finite threshold) → PEqNP, ¬SelfAppUnbounded
- SelfAppUnbounded → ¬PEqNP
- Specific pairings get specific results

The framework derives the classification from the pairing parameters.
No axioms. The connection to P_eq_NP comes through the specific
classical TM instantiation.

STATUS: 0 sorry.
-/

import ClassicalBridge.Complexity.Basic
import ClassicalBridge.Complexity.SemanticBridge
import ClassicalBridge.Bridge.ChainConnection
import ClassicalBridge.Mirror.CountingFunctions
import WTS.Tower.CarrierEngineering.MinimalNecessityGradient

namespace ClassicalBridge.Complexity.ModelCorrespondence

open ClassicalBridge.Complexity
open ClassicalBridge.Complexity.SemanticBridge
open ClassicalBridge.Bridge
open ClassicalBridge
open ClassicalBridge.TM
open WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The regime result — parameterized output
-- ════════════════════════════════════════════════════════════

/-- The regime classification result for a GRM.
    This is the OUTPUT of the framework, not an input. -/
structure RegimeResult (M : WTS.GradedReflModel) where
  /-- PEqNP holds or doesn't. -/
  peqnp : WTS.PEqNP M ∨ ¬WTS.PEqNP M
  /-- SelfAppUnbounded holds or doesn't. -/
  unbounded : WTS.SelfAppUnbounded M ∨ ¬WTS.SelfAppUnbounded M
  /-- If both PEqNP and SelfAppUnbounded: contradiction. -/
  incompatible : WTS.PEqNP M → WTS.SelfAppUnbounded M → False

/-- For a DriftedPairing: PEqNP holds, SelfAppUnbounded is refuted. -/
def RegimeResult.ofDriftedPairing (S : DriftedPairing) : RegimeResult S.M where
  peqnp := Or.inl (pairing_peqnp S)
  unbounded := Or.inr (fun hub => pairing_unbounded_absurd S hub)
  incompatible := fun _ hub => pairing_unbounded_absurd S hub

/-- For a SelfAppUnbounded model: ¬PEqNP. -/
def RegimeResult.ofUnbounded (M : WTS.GradedReflModel) (hub : WTS.SelfAppUnbounded M) :
    RegimeResult M where
  peqnp := Or.inr (fun ⟨d, hf⟩ => by
    obtain ⟨x, hle, hgt⟩ := hub.overflows d
    exact Nat.not_le.mpr hgt (hf x hle))
  unbounded := Or.inl hub
  incompatible := fun ⟨d, hf⟩ _ => by
    obtain ⟨x, hle, hgt⟩ := hub.overflows d
    exact Nat.not_le.mpr hgt (hf x hle)

-- ════════════════════════════════════════════════════════════
-- Section 2: classicalGRM instantiation
-- ════════════════════════════════════════════════════════════

variable (h : SelfAppHeader)

/-- classicalGRM as a WTS.GradedReflModel (type conversion). -/
noncomputable def classicalGRM_WTS : WTS.GradedReflModel where
  carrier := (classicalGRM h).carrier
  fold := (classicalGRM h).fold
  unfold := (classicalGRM h).unfold
  roundtrip := (classicalGRM h).roundtrip
  grade := (classicalGRM h).grade

/-- classicalGRM as a DriftedPairing. -/
noncomputable def classicalPairing : DriftedPairing where
  M := classicalGRM_WTS h
  threshold := bridgeOverhead h
  factors := fun x hle => by
    show (classicalGRM_WTS h).grade ((classicalGRM_WTS h).selfApp x) ≤ bridgeOverhead h
    exact classicalGRM_factorsThrough h x hle

/-- The regime result for classicalGRM: PEqNP, ¬SelfAppUnbounded. -/
noncomputable def classicalRegime : RegimeResult (classicalGRM_WTS h) :=
  RegimeResult.ofDriftedPairing (classicalPairing h)

-- ════════════════════════════════════════════════════════════
-- Section 3: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms classicalRegime

end ClassicalBridge.Complexity.ModelCorrespondence
