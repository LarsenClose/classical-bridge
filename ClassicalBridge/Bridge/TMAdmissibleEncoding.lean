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

STATUS: 0 sorry. Axiom profile: inherits classical_tm_exists and
classical_selfapp_header_exists from UniversalSimulation.lean.
-/

import ClassicalBridge.Mirror.AdmissibleEncoding
import ClassicalBridge.TuringMachine.UniversalSimulation

namespace ClassicalBridge.Bridge

open ClassicalBridge.TM

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

    AXIOM DEPENDENCY: This construction uses two axioms from
    UniversalSimulation.lean:
    1. classical_tm_exists (Turing 1936)
    2. classical_selfapp_header_exists (Kleene 1938)

    The structural theorems (roundtrip, grade bound) are PROVED,
    not axiomatized. The axioms only assert that the classical
    objects (TMs, self-application headers) exist. -/
noncomputable def classicalAdmissibleEncoding : AdmissibleEncoding where
  Names := BinString
  fold := bridgeFold
  unfold := bridgeUnfold
  roundtrip := bridge_roundtrip
  grade := grade
  overhead := bridgeOverhead
  selfApp_bounded := bridge_selfApp_bounded

-- ════════════════════════════════════════════════════════════
-- Derived: the induced GRM
-- ════════════════════════════════════════════════════════════

/-- The GradedReflModel induced by classical TM computation.
    This is the model in which the P vs NP regime question lives. -/
noncomputable def classicalGRM : GradedReflModel :=
  classicalAdmissibleEncoding.toGRM

/-- selfApp on the classical GRM is header ++ (x.drop headerLen):
    prepend the self-application header after stripping it.
    This is the TM self-interpretation operation at the
    description-length level. -/
theorem classicalGRM_selfApp_eq (x : BinString) :
    classicalGRM.selfApp x = bridgeUnfold (bridgeFold x) := rfl

/-- The classical GRM has finite drift at its overhead parameter.
    This is immediate from the AdmissibleEncoding construction. -/
theorem classicalGRM_finiteDrift :
    ∃ k, ∀ x, classicalGRM.grade (classicalGRM.selfApp x) ≤
              classicalGRM.grade x + k :=
  ⟨bridgeOverhead, bridge_selfApp_bounded⟩

-- ════════════════════════════════════════════════════════════
-- Axiom audit
-- ════════════════════════════════════════════════════════════

/-
AXIOM INVENTORY for classicalAdmissibleEncoding:

Custom axioms (from UniversalSimulation.lean):
1. classical_tm_exists : StepBoundedTM
2. classical_selfapp_header_exists : SelfAppHeader

Standard Lean axioms: propext, Quot.sound (from list operations).

The roundtrip and grade bound are THEOREMS, not axioms.
They follow from the definitions of tmFold (List.drop) and
tmUnfold (List.append) plus basic list arithmetic.

The custom axioms assert only EXISTENCE of classical objects
(TMs and self-application headers). They do not assert any
properties beyond what is built into the StepBoundedTM and
SelfAppHeader structures. The bridge properties (roundtrip,
grade bound) are structural consequences of the fold/unfold
definitions, not of the axioms.
-/

end ClassicalBridge.Bridge
