/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Bridge/TMAdmissibleEncoding.lean — THE MAIN THEOREM:
a standard TM-based computation model satisfies AdmissibleEncoding.

This is the formal bridge from classical complexity theory to the
carrier engineering framework. Once this is proved, all encoding-invariant
results (UnboundedGap, FiniteDrift, defect spectrum, least drift stability)
transfer automatically to the classical setting via BoundedGRMEquiv.

The construction assembles pieces from TuringMachine/UniversalSimulation.lean:
  Names := BinString (binary strings)
  fold := tmFold (strip fixed header)
  unfold := tmUnfold (prepend fixed header)
  roundtrip := tmFold_tmUnfold (proved)
  grade := List.length (description length)
  overhead := headerLen (the self-application header length)
  selfApp_bounded := selfApp_grade_bounded (proved)

STATUS: 0 sorry. Zero custom axioms. SelfAppHeader is a parameter;
classical_tm is proved in ConcreteModel.lean.
-/

import ClassicalBridge.Mirror.AdmissibleEncoding
import ClassicalBridge.TuringMachine.UniversalSimulation

namespace ClassicalBridge.Bridge

open ClassicalBridge.TM

variable (h : SelfAppHeader)

-- ════════════════════════════════════════════════════════════
-- THE MAIN THEOREM: Classical TM computation is an AdmissibleEncoding
-- ════════════════════════════════════════════════════════════

/-- THE CLASSICAL BRIDGE.

    A standard Turing machine computation model, with binary strings as
    the carrier and description length as the grade, satisfies the
    AdmissibleEncoding interface.

    This is the formal connection between classical complexity theory
    and the carrier engineering framework of witness-transport. Once
    this instance exists, all encoding-invariant results transfer:
    - UnboundedGap is invariant across same-semantics encodings
    - FiniteDrift existence is invariant
    - Least drift is stable up to 2 * overhead
    - The defect spectrum transfers with bounded distortion
    - The projectional classification applies

    CONSTRUCTION:
    - Names = List Bool (binary strings)
    - fold = strip the self-application header (tmFold)
    - unfold = prepend the self-application header (tmUnfold)
    - roundtrip: fold(unfold(x)) = drop(header ++ x) = x
    - grade = List.length (description length)
    - overhead = headerLen (a fixed constant, independent of input)
    - selfApp_bounded: grade(unfold(fold(x))) ≤ grade(x) + headerLen

    AXIOM DEPENDENCY: Zero custom axioms. classical_tm is proved
    via Mathlib's evaln (ConcreteModel.lean). SelfAppHeader is a
    parameter. The structural theorems (roundtrip, grade bound)
    are proved from the definitions. -/
noncomputable def classicalAdmissibleEncoding : AdmissibleEncoding where
  Names := BinString
  fold := bridgeFold h
  unfold := bridgeUnfold h
  roundtrip := bridge_roundtrip h
  grade := grade
  overhead := bridgeOverhead h
  selfApp_bounded := bridge_selfApp_bounded h

-- ════════════════════════════════════════════════════════════
-- Derived: the induced GRM
-- ════════════════════════════════════════════════════════════

/-- The GradedReflModel induced by classical TM computation.
    This is the model in which the P vs NP regime question lives. -/
noncomputable def classicalGRM : GradedReflModel :=
  (classicalAdmissibleEncoding h).toGRM

/-- selfApp on the classical GRM is header ++ (x.drop headerLen):
    prepend the self-application header after stripping it.
    This is the TM self-interpretation operation at the
    description-length level. -/
theorem classicalGRM_selfApp_eq (x : BinString) :
    (classicalGRM h).selfApp x = bridgeUnfold h (bridgeFold h x) := rfl

/-- The classical GRM has finite drift at its overhead parameter.
    This is immediate from the AdmissibleEncoding construction. -/
theorem classicalGRM_finiteDrift :
    ∃ k, ∀ x, (classicalGRM h).grade ((classicalGRM h).selfApp x) ≤
              (classicalGRM h).grade x + k :=
  ⟨bridgeOverhead h, bridge_selfApp_bounded h⟩

-- ════════════════════════════════════════════════════════════
-- Axiom audit
-- ════════════════════════════════════════════════════════════

/-
AXIOM INVENTORY for classicalAdmissibleEncoding:

Custom axioms: none.

- classical_tm is proved in ConcreteModel.lean (wraps Mathlib's
  Nat.Partrec.Code.evaln).
- SelfAppHeader is a parameter, not an axiom.

Standard Lean axioms: propext, Quot.sound, Classical.choice.

The roundtrip and grade bound are THEOREMS, not axioms.
They follow from the definitions of tmFold (List.drop) and
tmUnfold (List.append) plus basic list arithmetic.
-/

end ClassicalBridge.Bridge
