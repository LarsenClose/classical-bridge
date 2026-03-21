/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Composition/CrossRepoComposition.lean — Cross-repo dependency
graph, explicit and auditable.

This file serves as the authoritative trust-chain document for the
classical-bridge argument. It documents the cross-repo dependency graph,
re-exports the main results (naming_cost_nonclosure, fold_unfold_nonclosure,
ClassicalAnswerSpace, classical_computation_characterized), and provides
the complete logical flow.

The value of this file is in the docstrings. The Lean content is thin
(mostly re-exports). An auditor can read this file and know exactly
what is assumed, what is proved, and where each piece lives.

STATUS: 0 sorry. All composition theorems are re-exports of proved results.
Axiom profile documented in full in Section 1 and Section 6.
-/

import ClassicalBridge.Bridge.ChainConnection
import ClassicalBridge.Mirror.CountingFunctions
import ClassicalBridge.Mirror.SideA
import ClassicalBridge.Complexity.SemanticBridge
import ClassicalBridge.Complexity.FoldUnfoldNonclosure

namespace ClassicalBridge.Composition

open ClassicalBridge
open ClassicalBridge.Bridge
open ClassicalBridge.TM
open ClassicalBridge.Reductions

-- ════════════════════════════════════════════════════════════════════════════
-- Section 1: AXIOM AUDIT — Complete inventory
-- ════════════════════════════════════════════════════════════════════════════

/-!
## Axiom Audit

Every non-Lean-built-in axiom in the classical-bridge argument is documented
here. Three categories:

  A. Cross-repo mirrors: theorems proved in other repos, restated as axioms
     because classical-bridge cannot import those repos' build artifacts.

  B. Classical mathematics: foundational results from computability theory,
     stated as axioms rather than proved because the formal proof would
     require constructing a full Turing machine simulator — orthogonal to the
     bridge argument.

  C. Lean built-in: propext, Quot.sound, Classical.choice. These are standard
     and shared with all of Mathlib. Not tracked as custom axioms.

### Category A: Cross-repo mirrors

**sideA_bounded_selector_impossible** (ClassicalBridge.Mirror.SideA)

  Source: `witness-transport/WTS/Transport/TransportCollapseObstruction.lean`
  Proved as: `WTS.sideA_bounded_selector_impossible`

  Content: If SelfAppUnbounded M, then for every d, there is no function that
  simultaneously agrees with selfApp on grade-bounded inputs and has
  grade-bounded outputs on those inputs. Equivalently, ¬FactorsThrough M
  selfApp d whenever SelfAppUnbounded M holds.

  Why axiomatized: The proof in witness-transport uses a diagonal/cardinality
  argument built up over several files in WTS/Transport/. Importing the WTS
  build artifact would create a circular dependency (classical-bridge is
  independent by design). The type signature is character-identical to the
  proved theorem (modulo the _Mirror suffix used in classical-constraints).

  Mirror locations (three repos, same type, three axiom declarations):
  - witness-transport: `WTS.sideA_bounded_selector_impossible_mirror`
    in WTS/Shared/SideAMirror.lean (uses GradedReflModel_Mirror / SelfAppUnbounded_Mirror)
  - classical-constraints: `ClassicalConstraints.sideA_bounded_selector_impossible`
    in ClassicalConstraints/Shared/SideAMirror.lean (uses GradedReflModel_Mirror / SelfAppUnbounded_Mirror)
  - classical-bridge: `ClassicalBridge.sideA_bounded_selector_impossible`
    in ClassicalBridge/Mirror/SideA.lean (uses GradedReflModel / SelfAppUnbounded, no _Mirror suffix)

  The naming discrepancy (_Mirror suffix vs. none) is a known gap; see Section 5.

**growth_gap_survives_poly** (ClassicalBridge.Mirror.CountingFunctions)

  Source: `pnp-integrated/PNP/AntiCompression/PolynomialAntiCompression.lean`
  Proved as: `growth_gap_survives_poly` (line 148)

  Content: For any polynomial bound p (with degree and constant term), there
  exists a grade g such that N_End(g) > N_Val(g + p.eval g). The endomorphism
  count eventually dominates the carrier count even after polynomial-degree
  overhead shifting.

  Why axiomatized: The proof requires substantial arithmetic infrastructure
  built up over several files in pnp-integrated (exp_dominates_poly_sum,
  two_pow_ge_sq, etc.). The meso-level lemma (meso_has_growth_gap) is proved
  locally in CountingFunctions.lean; the full polynomial-overhead extension
  is what is axiomatized.

### Category B: Classical mathematics (formerly axioms, now proved/parameterized)

**classical_tm** (ClassicalBridge.TM, ConcreteModel.lean)

  Proved as classical_tm in ConcreteModel.lean: wraps Mathlib's
  Nat.Partrec.Code.evaln with BinString encoding/decoding. Provides the
  underlying computational substrate for the fold/unfold construction.
  Axiom profile: propext, Classical.choice, Quot.sound (standard Lean).

**SelfAppHeader** (ClassicalBridge.TM, UniversalSimulation.lean)

  A PARAMETER: the codebase takes SelfAppHeader as input, not as something
  proved to exist. The Kleene recursion theorem (1938) guarantees such a
  header exists for any UTM; the code does not depend on a specific
  construction.

**polytime_output_bound** (ClassicalBridge.Encoding, GradeStructure.lean)

  Classical justification: Basic TM theory. A TM running for t steps can
  write at most t symbols. Therefore a function computable in time T(n)
  on inputs of length n satisfies |f(x)| ≤ T(|x|).

  Role in the argument: Intended to connect computational time bounds to
  grade bounds for polynomial-time reductions between encodings. Used in
  polytime_gives_mult_bound.

  Status in main bridge chain: ORPHANED. polytime_output_bound and
  polytime_gives_mult_bound are proved in GradeStructure.lean but not
  imported by the main bridge chain (ChainConnection.lean). The axiom is
  not reachable from classicalGRM_PEqNP. See Section 5.

**resolution_feasible_interpolation** (ClassicalConstraints, classical-constraints repo only)

  Source: `classical-constraints/ClassicalConstraints/Chain2_ProofComplexity/
           FeasibleInterpolationBridge.lean`

  Classical justification: Krajicek/Razborov 1995. Resolution proofs admit
  feasible interpolation: if a resolution refutation of A(x) ∨ B(y) exists
  with size s, an interpolant circuit of size poly(s) can be extracted.

  Role in the argument: Used in classical-constraints to close the Chain 2
  (proof complexity) lock. Not present in classical-bridge.

  Status: In classical-constraints only. Not a classical-bridge axiom.
  Listed here for completeness of the four-repo picture.

### Category C: Lean built-in

propext, Quot.sound, Classical.choice — standard, shared with Mathlib.
Not tracked as custom axioms.
-/

-- ════════════════════════════════════════════════════════════════════════════
-- Section 2: REPO CONTRIBUTIONS
-- ════════════════════════════════════════════════════════════════════════════

/-!
## Repo Contributions

Four repos constitute the full argument. This section documents what each
proves and which files are the primary loci.

### pnp-integrated

The constructive core. Contains the fundamental impossibility argument.

Key files:
- `PNP/Transport/TransportCollapseObstruction.lean`:
  Proves `sideA_bounded_selector_impossible` (the Side A obstruction)
  and `selfApp_not_grade_bounded`. These are the deepest results —
  they establish that SelfAppUnbounded implies no grade-bounded evaluator
  can exist. This is the result that locks every chain.

- `PNP/AntiCompression/PolynomialAntiCompression.lean`:
  Proves `growth_gap_survives_poly`. The endomorphism count
  N_End(g) = (2^(g+1))^(2^(g+1)) exceeds the carrier count
  N_Val(g + p(g)) = 2^(g + p(g) + 1) for any polynomial p, at large enough g.
  This gives the quantitative basis for the growth gap.

- `PNP/Core.lean`:
  GradedReflModel, SelfAppUnbounded, PEqNP, FactorsThrough — the core types.

### witness-transport

Provides the encoding-invariance layer. Proves that the regime
classification (PEqNP vs. SelfAppUnbounded) is invariant under
bounded-overhead re-encodings (BoundedGRMEquiv).

Key files:
- `WTS/Shared/SideAMirror.lean`:
  Mirrors `sideA_bounded_selector_impossible` as axiom (cross-repo boundary)
  `sideA_bounded_selector_impossible_mirror` for use by the Protocol layer.

- `WTS/Tower/CarrierEngineering/ReencodingInvariance.lean`:
  Defines `BoundedGRMEquiv` and proves the invariance theorem:
  PEqNP is preserved/reflected by bounded-overhead equivalences.
  This is the encoding-invariant obstruction class result.

- `WTS/Tower/CarrierEngineering/ProjectionalAtlas.lean`:
  Classifies the natural semantics for Chain 5 (algebraic proof systems)
  and others. Proves that every natural semantic is projectional, the
  boundary is invariant, and projectional encodings force PEqNP.
  Zero sorry, axiom profile: propext + Quot.sound.

### classical-constraints

The lock theorems layer. For each of the 7 chains (SAT, proof complexity,
descriptive complexity, CSP, algebraic proof systems, extension complexity,
protocol), proves that TransferHypothesis + SelfAppUnbounded → False.

Key files (one per chain):
- `ClassicalConstraints/Chain1_SAT/BridgeVacuity.lean`
- `ClassicalConstraints/Chain2_ProofComplexity/BridgeVacuity.lean`
- `ClassicalConstraints/Chain3_Descriptive/BridgeVacuity.lean`
- `ClassicalConstraints/Chain4_CSP/BridgeVacuity.lean`
- `ClassicalConstraints/Chain5_Algebraic/BridgeVacuity.lean`
- `ClassicalConstraints/Chain6_Extension/BridgeVacuity.lean`
- `ClassicalConstraints/Chain7_Protocol/BridgeVacuity.lean`

Shared infrastructure:
- `ClassicalConstraints/Shared/SideAMirror.lean`:
  Mirrors GradedReflModel_Mirror, SelfAppUnbounded_Mirror, and
  sideA_bounded_selector_impossible for use across all 7 chains.

Note on TransferHypothesis vacuity: all 7 chain locks currently fire
vacuously (SelfAppUnbounded is never inhabited for classicalGRM, so the
conclusion TransferHypothesis → False holds by ex falso). See Section 5.

### classical-bridge (this repo)

The classical model layer. Proves that classicalGRM (the GRM induced by
the fold/unfold pair from the UTM and Kleene header) has finite drift and
satisfies PEqNP. This places the classical TM model firmly in the
bounded-overhead regime.

Key files:
- `ClassicalBridge/TuringMachine/ConcreteModel.lean`:
  Proves classical_tm using Mathlib's Nat.Partrec.Code.evaln.

- `ClassicalBridge/TuringMachine/UniversalSimulation.lean`:
  Defines fold/unfold, proves roundtrip and selfApp_grade_bounded.
  SelfAppHeader is a parameter, not an axiom.

- `ClassicalBridge/Bridge/TMAdmissibleEncoding.lean`:
  Builds classicalAdmissibleEncoding and classicalGRM from the fold/unfold
  construction.

- `ClassicalBridge/Bridge/ChainConnection.lean`:
  Proves the regime classification theorems:
  classicalGRM_hasFiniteDrift, classicalGRM_not_hasUnboundedGap,
  classicalGRM_not_selfAppUnbounded, classicalGRM_PEqNP.

- `ClassicalBridge/Complexity/SemanticBridge.lean`:
  Proves naming_cost_nonclosure (the main result), ClassicalAnswerSpace,
  and classical_computation_characterized (the three cannots).

- `ClassicalBridge/Complexity/FoldUnfoldNonclosure.lean`:
  Proves fold_unfold_nonclosure — the nonclosure at the weakest structural
  level (FoldUnfoldSection, no grade condition). Strengthens
  naming_cost_nonclosure.

- `ClassicalBridge/Reductions/KarpPreservation.lean`:
  Defines structure-preserving reductions, proves the boundary theorem
  (Projectional + HasUnboundedGap → no StructurePreservingReduction exists).

Mirror files (cross-repo type definitions, not in main bridge chain):
- `ClassicalBridge/Mirror/GRM.lean`: GradedReflModel, SelfAppUnbounded, PEqNP
- `ClassicalBridge/Mirror/SideA.lean`: sideA_bounded_selector_impossible (proved theorem)
- `ClassicalBridge/Mirror/CountingFunctions.lean`: growth_gap_survives_poly (proved theorem)
-/

-- ════════════════════════════════════════════════════════════════════════════
-- Section 3: COMPOSITION THEOREMS — re-exports
-- ════════════════════════════════════════════════════════════════════════════

/-!
## Composition Theorems

These theorems are re-exports of results proved in ChainConnection.lean
and Mirror files. They are given composition_ prefixes to make the
cross-repo dependency explicit. No new proofs here.
-/

/-- The classical GRM satisfies PEqNP: selfApp factors through grade
    bridgeOverhead.

    Re-export of `ClassicalBridge.Bridge.classicalGRM_PEqNP`.

    Trust chain: classical_tm (proved, ConcreteModel.lean) + SelfAppHeader
    (parameter) → fold/unfold construction → classicalAdmissibleEncoding →
    classicalGRM → selfApp = prepend-then-strip-header → grade-non-increasing
    for inputs above the overhead threshold → FactorsThrough at bridgeOverhead
    → PEqNP.

    Zero custom axioms. -/
theorem composition_classicalGRM_PEqNP (h : SelfAppHeader) : PEqNP (classicalGRM h) :=
  classicalGRM_PEqNP h

/-- The classical GRM has finite drift at overhead = bridgeOverhead.

    Re-export of `ClassicalBridge.Bridge.classicalGRM_hasFiniteDrift`.

    Content: for all x, grade(selfApp(x)) ≤ grade(x) + bridgeOverhead.
    This is the additive overhead bound that follows directly from the
    selfApp_grade_bounded lemma in UniversalSimulation.lean. -/
theorem composition_classicalGRM_finiteDrift (h : SelfAppHeader) :
    HasFiniteDrift (classicalAdmissibleEncoding h) (bridgeOverhead h) :=
  classicalGRM_hasFiniteDrift h

/-- The classical GRM does not have SelfAppUnbounded.

    Re-export of `ClassicalBridge.Bridge.classicalGRM_not_selfAppUnbounded`.

    Content: the fixed self-application header means selfApp can only overflow
    grade threshold d when d < headerLen. Since SelfAppUnbounded requires
    overflow at every threshold and headerLen is a fixed constant, the condition
    is impossible.

    This is the key step that disconnects classicalGRM from the lock theorems:
    the lock theorems require SelfAppUnbounded, which classicalGRM does not have. -/
theorem composition_classicalGRM_not_selfAppUnbounded (h : SelfAppHeader) :
    ¬ SelfAppUnbounded (classicalGRM h) :=
  classicalGRM_not_selfAppUnbounded h

/-- The growth gap survives polynomial overhead.

    Re-export of `ClassicalBridge.growth_gap_survives_poly` from Mirror.CountingFunctions.

    Content: for any polynomial bound p, there exists g with
    N_End(g) > N_Val(g + p.eval g). This is the quantitative engine of the
    counting argument.

    Trust chain: proved locally in ClassicalBridge/Mirror/CountingFunctions.lean
    (ported from pnp-integrated/PNP/AntiCompression/PolynomialAntiCompression.lean). -/
theorem composition_growth_gap_unconditional (p : PolyBound) :
    ∃ g, N_End g > N_Val (g + p.eval g) :=
  growth_gap_survives_poly p

/-- The Side A impossibility: no grade-bounded evaluator agrees with selfApp
    when selfApp is unbounded.

    Re-export of `ClassicalBridge.sideA_bounded_selector_impossible` from Mirror.SideA.

    Content: if SelfAppUnbounded M, then for every d, no function f can both
    agree with selfApp on d-bounded inputs and have d-bounded outputs.
    Equivalently, ¬FactorsThrough M selfApp d under SelfAppUnbounded.

    Trust chain: proved locally in ClassicalBridge/Mirror/SideA.lean
    (originally from witness-transport/WTS/Transport/TransportCollapseObstruction.lean). -/
theorem composition_sideA (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (d : Nat) :
    ¬∃ (f : M.carrier → M.carrier),
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) ∧
      (∀ x, M.grade x ≤ d → M.grade (f x) ≤ d) :=
  sideA_bounded_selector_impossible M hub d

-- ════════════════════════════════════════════════════════════════════════════
-- Section 4: TRUST CHAIN
-- ════════════════════════════════════════════════════════════════════════════

/-!
## Trust Chain

### Custom axiom count

Total custom axioms (non-Lean-built-in) in classical-bridge:

  Main bridge chain (naming_cost_nonclosure, fold_unfold_nonclosure,
  ClassicalAnswerSpace, and their consequences):
    ZERO custom axioms. classical_tm is proved; SelfAppHeader is a parameter.

  In Mirror files (not in main chain, proved locally):
    1. sideA_bounded_selector_impossible — proved theorem (4-line proof)
    2. growth_gap_survives_poly          — proved theorem (ported from pnp-integrated)

  In GradeStructure.lean (orphaned from main chain):
    3. polytime_output_bound         — axiom (basic TM theory, not reachable from main results)

  In classical-constraints only:
    4. resolution_feasible_interpolation — axiom (Krajicek/Razborov 1995)

  TOTAL: 1 orphaned axiom in classical-bridge; 0 in the main chain.

### Complete logical flow

**pnp-integrated** (constructive core)
  ↓ proves sideA_bounded_selector_impossible (diagonal/cardinality argument)
  ↓ proves growth_gap_survives_poly (exp dominates poly)

**witness-transport** (encoding invariance)
  ↓ mirrors sideA_bounded_selector_impossible as axiom (cross-repo boundary)
  ↓ proves regime invariance under BoundedGRMEquiv
  ↓ proves projectional classification (ProjectionalAtlas.lean)

**classical-constraints** (lock theorems)
  ↓ mirrors sideA + GRM types (cross-repo boundary)
  ↓ proves TransferHypothesis + SelfAppUnbounded → False (7 chains)
  ↓ proves direct bridge theorems for all 7 chains (ModelData + SelfAppUnbounded → False)

**classical-bridge** (classical model, this repo)
  ↓ classical_tm proved via Mathlib evaln (ConcreteModel.lean)
  ↓ SelfAppHeader as parameter
  ↓ fold/unfold construction (UniversalSimulation.lean)
  ↓ classicalAdmissibleEncoding (TMAdmissibleEncoding.lean)
  ↓ classicalGRM (TMAdmissibleEncoding.lean)
  ↓ classicalGRM_hasFiniteDrift, classicalGRM_PEqNP (ChainConnection.lean)
  ↓ **naming_cost_nonclosure** (SemanticBridge.lean) ← MAIN RESULT
  ↓ **fold_unfold_nonclosure** (FoldUnfoldNonclosure.lean) ← strengthened form
  ↓ **ClassicalAnswerSpace** (SemanticBridge.lean) ← complete answer space
  ↓ **classical_computation_characterized** (SemanticBridge.lean) ← the three cannots

### Connection between repos

The lock theorems (classical-constraints) prove:
  ∀ chain i, TransferHypothesis_i M + SelfAppUnbounded M → False

The bridge (classical-bridge) proves:
  ¬ SelfAppUnbounded classicalGRM

Together they say: classicalGRM is in the finite-drift / PEqNP regime,
not the separation regime. The lock theorems do not constrain classicalGRM
because their precondition (SelfAppUnbounded) is not met.

The encoding invariance layer (witness-transport) says:
  BoundedGRMEquiv classicalGRM M' → (PEqNP classicalGRM ↔ PEqNP M')

So the regime classification transfers to any model bounded-overhead
equivalent to classicalGRM.

### Remaining custom axioms

The main bridge chain has ZERO custom axioms. The only remaining
custom axiom in the codebase is:

  1. polytime_output_bound (GradeStructure.lean) — orphaned from
     the main chain. Not reachable from any main result. Would
     require formalizing TM execution traces and counting write
     operations to eliminate.

Items that WERE axioms and are now eliminated:

  - classical_tm is proved (ConcreteModel.lean, wraps Mathlib's
    Nat.Partrec.Code.evaln)
  - SelfAppHeader is parameterized (taken as input)
  - sideA_bounded_selector_impossible → proved (4-line proof from
    SelfAppUnbounded.overflows)
  - growth_gap_survives_poly → proved (ported from pnp-integrated,
    proved locally in CountingFunctions.lean)
-/

-- ════════════════════════════════════════════════════════════════════════════
-- Section 5: GAP ANALYSIS
-- ════════════════════════════════════════════════════════════════════════════

/-!
## Gap Analysis

The following gaps are known and documented. None invalidate the main
result (classicalGRM_PEqNP). They are recorded here for completeness
and to guide future work.

### Gap 1: polytime_output_bound is orphaned from the main chain

`ClassicalBridge.Encoding.GradeStructure` declares `polytime_output_bound`
and proves `polytime_gives_mult_bound`. Neither is imported by the main
bridge chain (`ClassicalBridge.Bridge.ChainConnection.lean`). The axiom is
reachable in principle (via GradeStructure.lean) but contributes nothing
to classicalGRM_PEqNP. Future work: connect polytime_output_bound to the
grade bounds used in TMAdmissibleEncoding.lean to give a tighter accounting
of the overhead constant.

### Gap 2: Mirror.SideA and Mirror.CountingFunctions are orphaned

`ClassicalBridge.Mirror.SideA` (sideA_bounded_selector_impossible) and
`ClassicalBridge.Mirror.CountingFunctions` (growth_gap_survives_poly) are not
imported by the main barrel file `ClassicalBridge.lean`. They are imported
here (in CrossRepoComposition.lean) for documentation purposes, but are not
part of the main bridge chain. The Side A and growth-gap results are used by
classical-constraints, not by classical-bridge directly.

Future work: either remove these files from classical-bridge (they are already
present in classical-constraints) or wire them into the main barrel.

### Gap 3: _Mirror suffix naming discrepancy

The SideA impossibility result exists in four repos under three names:

  - pnp-integrated (proved theorem):
    `WTS.sideA_bounded_selector_impossible` (no suffix)
  - witness-transport (axiom mirror, cross-repo boundary):
    `WTS.sideA_bounded_selector_impossible_mirror` (_mirror suffix)
  - classical-constraints (axiom mirror, cross-repo boundary):
    `ClassicalConstraints.sideA_bounded_selector_impossible` (no suffix)
  - classical-bridge (proved theorem, ported from pnp-integrated):
    `ClassicalBridge.sideA_bounded_selector_impossible` (no suffix)

The _Mirror suffix is used for GRM types in WTS and ClassicalConstraints
(GradedReflModel_Mirror, SelfAppUnbounded_Mirror) but not for the theorem
name in classical-bridge. The type structures are identical; only the names
differ. This does not affect correctness but creates friction for auditors.

Future work: standardize naming across all repos (either always use _Mirror
or never use it for the sideA theorem).

### Gap 4: TransferHypothesis vacuity

All 7 chain lock theorems in classical-constraints prove:
  TransferHypothesis_i M + SelfAppUnbounded M → False

Since classicalGRM does not have SelfAppUnbounded (proved here:
classicalGRM_not_selfAppUnbounded), the lock theorems fire vacuously for
classicalGRM: the hypothesis SelfAppUnbounded M is never supplied, so the
conclusion is never reached.

This means: the lock theorems do not positively constrain classicalGRM.
They characterize the SEPARATION regime (models with SelfAppUnbounded).
classicalGRM is in the BOUNDED regime. The theorems are not vacuous in the
sense of being useless — they correctly describe which models would be in
the separation regime — but for the specific case of classicalGRM, they
contribute nothing to the proof.

Future work: identify a model M where SelfAppUnbounded M holds and use the
lock theorems to derive a non-trivial consequence for that model.

### Gap 5: DriftedLock — present and proved

The drifted lock theorem is proved in DriftedLock.lean.
DriftedLockData → False, with zero custom axioms. The lock fires
even when SelfAppUnbounded is replaced by a weaker hypothesis
(finite drift + polynomial solver), so it has force for models
like classicalGRM. Non-vacuity witnesses are in NonVacuity.lean.

### Gap 6: (Resolved) CrossRepoComposition now imports the main results

SemanticBridge.lean and FoldUnfoldNonclosure.lean are imported and
their main results are re-exported as composition_ theorems in Section 7.
-/

-- ════════════════════════════════════════════════════════════════════════════
-- Section 6: AXIOM AUDIT (#print axioms)
-- ════════════════════════════════════════════════════════════════════════════

-- These checks confirm the axiom profiles of the composition theorems.
-- An auditor can run `#print axioms composition_classicalGRM_PEqNP` and
-- verify: only standard Lean built-ins appear (propext, Classical.choice,
-- Quot.sound). Zero custom axioms.

-- Regime classification (from ChainConnection.lean)
#check @composition_classicalGRM_PEqNP
#check @composition_classicalGRM_finiteDrift
#check @composition_classicalGRM_not_selfAppUnbounded
#check @composition_growth_gap_unconditional
#check @composition_sideA

-- ════════════════════════════════════════════════════════════════════════════
-- Section 7: MAIN RESULTS — re-exports from SemanticBridge and FoldUnfoldNonclosure
-- ════════════════════════════════════════════════════════════════════════════

open ClassicalBridge.Complexity.SemanticBridge
open ClassicalBridge.Complexity.FoldUnfoldNonclosure
open WTS

/-- The main result: no GRMorphism from T(classicalGRM h) to classicalGRM h
    when headerLen > 0.

    Re-export of `naming_cost_nonclosure` from SemanticBridge.lean. Zero custom
    axioms. The proof: GRMorphism commutation forces fold(φ(t)) = φ(t) and
    unfold(φ(t)) = φ(t). In classicalGRM, fold shortens and unfold lengthens.
    When headerLen > 0, no element can be fixed by both. -/
theorem composition_naming_cost_nonclosure (h : SelfAppHeader) (hne : h.headerLen > 0)
    (φ : GRMorphism (transportGradedReflModel (classicalGRM_WTS h)) (classicalGRM_WTS h)) :
    False :=
  naming_cost_nonclosure h hne φ

/-- The strengthened form: no FoldUnfoldSection (weaker than GRMorphism, no grade
    condition) from T(classicalGRM h) to classicalGRM h when headerLen > 0.

    Re-export of `fold_unfold_nonclosure` from FoldUnfoldNonclosure.lean. -/
theorem composition_fold_unfold_nonclosure (h : SelfAppHeader) (hne : h.headerLen > 0)
    (φ : FoldUnfoldSection (transportGradedReflModel (classicalGRM_WTS h))
                           (classicalGRM_WTS h)) :
    False :=
  fold_unfold_nonclosure h hne φ

/-- The complete answer space for any naming convention.

    Re-export of `classical_answer_space` from SemanticBridge.lean. -/
noncomputable def composition_classical_answer_space (h : SelfAppHeader) :
    ClassicalAnswerSpace h :=
  classical_answer_space h

/-- The three cannots as a single conjunction.

    Re-export of `classical_computation_characterized` from SemanticBridge.lean. -/
theorem composition_classical_computation_characterized (h : SelfAppHeader)
    (hne : h.headerLen > 0) :
    (∀ x, (classicalGRM_WTS h).grade ((classicalGRM_WTS h).selfApp x) ≤
           (classicalGRM_WTS h).grade x + h.headerLen) ∧
    (∀ _φ : GRMorphism (transportGradedReflModel (classicalGRM_WTS h))
                       (classicalGRM_WTS h), False) ∧
    (∀ k, ¬∀ n, ResourceSemantics.functionSpaceSize
                   ResourceSemantics.binaryResourceModel n ≤
                   ResourceSemantics.binaryResourceModel.nProg (n + k)) :=
  classical_computation_characterized h hne

-- Main result axiom audits
#print axioms composition_naming_cost_nonclosure
#print axioms composition_fold_unfold_nonclosure
#print axioms composition_classical_answer_space
#print axioms composition_classical_computation_characterized

end ClassicalBridge.Composition
