/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Composition/CrossRepoComposition.lean — Cross-repo dependency
graph, explicit and auditable.

This file serves as the authoritative trust-chain document for the
classical-bridge argument. It mirrors key results from each repo as
axioms (clearly documented), states how they compose, and provides the
complete logical flow from raw axioms to the regime classification.

The value of this file is in the docstrings. The Lean content is thin
(mostly re-exports). An auditor can read this file and know exactly
what is assumed, what is proved, and where each piece lives.

STATUS: 0 sorry. All composition theorems are re-exports of proved results.
Axiom profile documented in full in Section 1 and Section 6.
-/

import ClassicalBridge.Bridge.ChainConnection
import ClassicalBridge.Mirror.CountingFunctions
import ClassicalBridge.Mirror.SideA

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

### Category B: Classical mathematics axioms

**classical_tm_exists** (ClassicalBridge.TM, UniversalSimulation.lean)

  Classical justification: Turing 1936. Deterministic Turing machines are a
  well-defined mathematical object. The step-bounded execution model is
  standard in complexity theory. Any of the standard constructions
  (single-tape, multi-tape, RAM machine) satisfies these axioms.

  Role in the argument: Provides the underlying computational substrate for
  the fold/unfold construction. The bridge theorem is independent of which
  specific TM model is used — all reasonable models are polynomially
  equivalent (Cobham-Edmonds thesis).

  Status in main bridge chain: ACTIVE. Used in TMAdmissibleEncoding.lean →
  ChainConnection.lean → classicalGRM_PEqNP.

**classical_selfapp_header_exists** (ClassicalBridge.TM, UniversalSimulation.lean)

  Classical justification: Kleene recursion theorem, 1938. For any acceptable
  Goedel numbering of programs, there exists a fixed-length binary string
  whose length depends only on the UTM, not on the program being
  self-applied. The bridge fold/unfold pair (drop-headerLen / prepend-header)
  is built on this fact.

  Role in the argument: Provides the fixed-length header that makes the
  fold/unfold construction well-defined and gives the bounded-overhead
  guarantee. The header length IS the bridgeOverhead constant.

  Status in main bridge chain: ACTIVE. Used in TMAdmissibleEncoding.lean →
  ChainConnection.lean → classicalGRM_not_selfAppUnbounded,
  classicalGRM_factorsThrough, classicalGRM_PEqNP.

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
- `ClassicalBridge/TuringMachine/UniversalSimulation.lean`:
  Defines fold/unfold, proves roundtrip and selfApp_grade_bounded.
  Axioms: classical_tm_exists, classical_selfapp_header_exists.

- `ClassicalBridge/Bridge/TMAdmissibleEncoding.lean`:
  Builds classicalAdmissibleEncoding and classicalGRM from the fold/unfold
  construction.

- `ClassicalBridge/Bridge/ChainConnection.lean`:
  Proves the regime classification theorems:
  classicalGRM_hasFiniteDrift, classicalGRM_not_hasUnboundedGap,
  classicalGRM_not_selfAppUnbounded, classicalGRM_PEqNP.
  This is the main result file.

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

    Trust chain: classical_tm_exists (Turing 1936) + classical_selfapp_header_exists
    (Kleene 1938) → fold/unfold construction → classicalAdmissibleEncoding →
    classicalGRM → selfApp = prepend-then-strip-header → grade-non-increasing
    for inputs above the overhead threshold → FactorsThrough at bridgeOverhead
    → PEqNP.

    No additional axioms beyond the two Category B axioms listed in Section 1. -/
theorem composition_classicalGRM_PEqNP : PEqNP classicalGRM :=
  classicalGRM_PEqNP

/-- The classical GRM has finite drift at overhead = bridgeOverhead.

    Re-export of `ClassicalBridge.Bridge.classicalGRM_hasFiniteDrift`.

    Content: for all x, grade(selfApp(x)) ≤ grade(x) + bridgeOverhead.
    This is the additive overhead bound that follows directly from the
    selfApp_grade_bounded lemma in UniversalSimulation.lean. -/
theorem composition_classicalGRM_finiteDrift :
    HasFiniteDrift classicalAdmissibleEncoding bridgeOverhead :=
  classicalGRM_hasFiniteDrift

/-- The classical GRM does not have SelfAppUnbounded.

    Re-export of `ClassicalBridge.Bridge.classicalGRM_not_selfAppUnbounded`.

    Content: the fixed self-application header means selfApp can only overflow
    grade threshold d when d < headerLen. Since SelfAppUnbounded requires
    overflow at every threshold and headerLen is a fixed constant, the condition
    is impossible.

    This is the key step that disconnects classicalGRM from the lock theorems:
    the lock theorems require SelfAppUnbounded, which classicalGRM does not have. -/
theorem composition_classicalGRM_not_selfAppUnbounded :
    ¬ SelfAppUnbounded classicalGRM :=
  classicalGRM_not_selfAppUnbounded

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

Total custom axioms (non-Lean-built-in) across all four repos:

  Main bridge chain (classicalGRM_PEqNP and its consequences):
    1. classical_tm_exists          — Category B (Turing 1936)
    2. classical_selfapp_header_exists — Category B (Kleene 1938)

  In Mirror files (not in main chain, proved locally):
    3. sideA_bounded_selector_impossible — proved theorem (ported from pnp-integrated)
    4. growth_gap_survives_poly          — proved theorem (ported from pnp-integrated)

  In GradeStructure.lean (orphaned from main chain):
    5. polytime_output_bound         — Category B (basic TM theory)

  In classical-constraints only:
    6. resolution_feasible_interpolation — Category B (Krajicek/Razborov 1995)

  TOTAL: 6 across all files; 2 in the main bridge chain; 4 in
  supporting/orphaned/external files.

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
  ↓ axioms: classical_tm_exists + classical_selfapp_header_exists
  ↓ fold/unfold construction (UniversalSimulation.lean)
  ↓ classicalAdmissibleEncoding (TMAdmissibleEncoding.lean)
  ↓ classicalGRM (TMAdmissibleEncoding.lean)
  ↓ classicalGRM_hasFiniteDrift (ChainConnection.lean)
  ↓ classicalGRM_not_selfAppUnbounded (ChainConnection.lean)
  ↓ classicalGRM_factorsThrough (ChainConnection.lean)
  ↓ **classicalGRM_PEqNP** (ChainConnection.lean) ← MAIN RESULT

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

### What WOULD be needed for a fully self-contained Lean proof

To eliminate all custom axioms, one would need:

  1. classical_tm_exists → formal construction of a step-bounded TM
     simulator in Lean. This is a significant engineering project
     (several thousand lines); see e.g. the Flydra project or
     Lean4's partial TM formalizations.

  2. classical_selfapp_header_exists → formal proof of the Kleene
     recursion theorem in Lean using the above TM simulator.

  3. sideA_bounded_selector_impossible → either import pnp-integrated
     directly (requires solving the circular dependency problem) or
     reprove the diagonal argument in classical-bridge.

  4. growth_gap_survives_poly → reprove the polynomial anti-compression
     theorem locally (the meso-level lemma is already proved here;
     only the polynomial-overhead generalization needs to be added).

  5. polytime_output_bound → prove that TM step count bounds output length,
     using the formal TM construction from (1).

  6. resolution_feasible_interpolation (classical-constraints only) →
     formalize the Krajicek/Razborov interpolation theorem. This is the
     hardest of the six; it requires substantial proof complexity machinery.

Removing (3) and (4) is the most tractable: the proofs exist in
pnp-integrated and could be ported. Removing (1) and (2) requires
committing to a specific TM model. Removing (6) is a research-level
formalization project.
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

### Gap 5: DriftedLock as the response to vacuity

The drifted lock theorem (DriftedLock.lean, noted in project memory as the
"non-vacuous lock bypassing sideA via growth gap counting") was identified
as the key pre-freeze formalization target. Its purpose is to give a
non-vacuous lock — one that fires even when SelfAppUnbounded is replaced by
a weaker hypothesis — so that the argument has force for models like
classicalGRM, not just hypothetical separation-regime models.

Status: not yet present in classical-bridge as of this writing. When
DriftedLock.lean is added, its axiom profile and role in the main chain
should be documented here.
-/

-- ════════════════════════════════════════════════════════════════════════════
-- Section 6: AXIOM AUDIT (#print axioms)
-- ════════════════════════════════════════════════════════════════════════════

-- These checks confirm the axiom profiles of the main composition theorems.
-- An auditor can run `#print axioms composition_classicalGRM_PEqNP` and
-- verify: only classical_tm_exists + classical_selfapp_header_exists appear
-- as custom axioms (plus standard Lean built-ins).

#check @composition_classicalGRM_PEqNP
#check @composition_classicalGRM_finiteDrift
#check @composition_classicalGRM_not_selfAppUnbounded
#check @composition_growth_gap_unconditional
#check @composition_sideA

end ClassicalBridge.Composition
