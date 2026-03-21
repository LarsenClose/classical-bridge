/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Complexity/PolyMarkovConnection.lean — Supporting material
for the PolyMarkov / counting-level connection.

This file is NOT part of the main theorem chain (naming_cost_nonclosure,
fold_unfold_nonclosure, ClassicalAnswerSpace, classical_computation_characterized).
It provides supporting infrastructure for the counting-level argument.

## Contents

  counting_engine_unconditional — re-export of construction_super_poly:
  no polynomial bound makes N_End(g) ≤ N_Val(g + p(g)) for all g.

  PEqNP_nat_gives_compModel_finder — if PEqNP_nat holds, a CompModel
  finder exists for any NatNP language. This is the Nat-level half of the
  counting connection; it does not by itself yield ¬P_eq_NP.

## Relationship to main chain

The main P != NP argument routes through naming_cost_nonclosure
(SemanticBridge.lean) — the structural incompatibility between the
transport tower and the classical carrier. This file's counting-level
infrastructure is a quantitative shadow of that structural result.

STATUS: 0 sorry.
-/

import ClassicalBridge.Complexity.Basic
import ClassicalBridge.Bridge.PolyMarkovBridge
import ClassicalBridge.Complexity.ModelCorrespondence

namespace ClassicalBridge.Complexity.PolyMarkovConnection

open ClassicalBridge.Complexity
open ClassicalBridge.TM
open ClassicalBridge
open ClassicalBridge.Bridge.PolyMarkovBridge
open ClassicalBridge.Bridge
open ClassicalBridge.Complexity.ModelCorrespondence

-- ════════════════════════════════════════════════════════════
-- Section 1: Regime classification and counting engine
-- ════════════════════════════════════════════════════════════

/-!
## Regime classification via DriftedPairing

The old monolithic chain (P_eq_NP → bridge_injection → counting → False)
has been replaced by the parameterized DriftedPairing framework
(SemanticBridge.lean, ModelCorrespondence.lean). The regime classification
is now a parameterized outcome: feed in the model-semantics pairing,
get the regime result. P_eq_NP determines specific parameters (the
polynomial from the algorithm it asserts exists); the counting engine
(construction_super_poly) refutes any polynomial.

The proved components:
- classicalRegime: RegimeResult for classicalGRM (zero custom axioms)
- construction_super_poly: ∀ p, ¬PolyBoundedConstruction N_End N_Val p
- classicalGRM_factorsThrough: selfApp factors through bridgeOverhead
- binary_has_growth_gap: ∀ c, ∃ g, N_End g > N_Val(g + c)
-/

/-- The counting engine is unconditional: no polynomial bound works. -/
theorem counting_engine_unconditional :
    ∀ p : PolyBound, ¬ PolyBoundedConstruction N_End N_Val p :=
  construction_super_poly

-- ════════════════════════════════════════════════════════════
-- Section 5: Connection to the NatNP formulation
-- ════════════════════════════════════════════════════════════

/-!
## Connection to NatNP and PEqNP_nat

Basic.lean defines NatNP and PEqNP_nat as the Nat-level versions.
We show the relationship: PEqNP_nat implies the existence of a CompModel
satisfying PolyMarkovProp (at least the "finder exists" direction).

Note: PEqNP_nat as defined in Basic.lean returns the finder in a potentially
different model from the verifier. PolyMarkovProp requires the same model.
The model correspondence is now handled via peqnp_counting_correspondence
in ModelCorrespondence.lean, which bridges P_eq_NP directly to the counting
impossibility without requiring an intermediate PolyMarkovProp.
-/

/-- PEqNP_nat implies PolyMarkovProp for a CompModel built directly from
    a NatNP language's verifier data.

    Given NatNP L (verifier run, mono, p_ver, cert_poly, time_poly),
    the CompModel with Prog = Nat and run = run satisfies a restricted form
    of PolyMarkovProp: for the specific verifier p_ver with bound time_poly,
    PEqNP_nat gives a finder.

    This is the Nat-level half of the connection. The gap to full PolyMarkovProp
    (which quantifies over ALL verifiers in the model, not just p_ver) is filled
    by peqnp_counting_correspondence in ModelCorrespondence.lean. -/
theorem PEqNP_nat_gives_compModel_finder
    (h : PEqNP_nat)
    (L : NatLanguage) (hL : NatNP L) :
    ∃ (M : CompModel) (finder : M.Prog) (q : PolyBound),
      ∀ x, ∃ w t, t ≤ q.eval x ∧ M.run finder x t = some w := by
  obtain ⟨run, hmono, p_ver, cert_poly, time_poly, _hverif⟩ := hL
  -- Apply PEqNP_nat to get a finder in some (run', ...) model
  obtain ⟨run', hmono', finder, q, hfind⟩ := h L ⟨run, hmono, p_ver, cert_poly, time_poly, _hverif⟩
  -- Build the CompModel from run'
  exact ⟨⟨Nat, run', hmono'⟩, finder, q, hfind⟩

end ClassicalBridge.Complexity.PolyMarkovConnection
