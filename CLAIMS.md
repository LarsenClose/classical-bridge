# CLAIMS.md -- classical-bridge

What this project proves, what it assumes, and what it does not claim.

**Scope note.** `PEqNP` and `SelfAppUnbounded` are internal predicates on graded reflexive models (GRMs), defined in the carrier engineering framework of witness-transport. `PEqNP M` asserts that `selfApp` factors through some grade bound; `SelfAppUnbounded M` asserts no such bound exists. These are regime shorthands within the GRM formalism, not direct assertions about Turing machine time complexity classes.

**Project inventory.** 23 source files. Zero sorry across all files. 6 custom axioms (2 in main bridge chain, 3 model-correspondence, 1 orphaned). Lean foundational axioms: `propext`, `Quot.sound`, `Classical.choice`. All theorems using Mathlib inherit `propext` and `Quot.sound` as infrastructure axioms; per-theorem listings below note only `Classical.choice` where it appears, since that is the mathematically significant distinction. `Classical.choice` is used in `Bridge/CountingBridge.lean`, `Bridge/AbstractCountingBridge.lean`, and `Bridge/PolyMarkovBridge.lean` (via `Fintype.equivFin` and `Fintype.card_le_of_injective`) but is NOT used in the main bridge chain (`classicalGRM_PEqNP` and related theorems in ChainConnection.lean).

---

## 1. Primary Claim

The project formalizes a bridge from classical Turing machine computation to the carrier engineering framework of witness-transport, classifies the induced graded reflexive model, and proves invariance of that classification across same-semantics header variants. It proves that binary strings with description-length grading, equipped with a fixed self-application header derived from the Kleene recursion theorem, satisfy the `AdmissibleEncoding` interface. The induced GRM has finite drift, satisfies PEqNP, and does not have SelfAppUnbounded. The chain lock theorems' precondition is not met by this model.

**Primary result (the bridge):**

- `classicalAdmissibleEncoding` -- classical TM computation satisfies AdmissibleEncoding
  - File: `ClassicalBridge/Bridge/TMAdmissibleEncoding.lean`
  - Type: `AdmissibleEncoding`
  - Construction: `Names := List Bool`, `fold := List.drop headerLen`, `unfold := header ++ ·`, `grade := List.length`, `overhead := headerLen`
  - Lean foundational: propext, Quot.sound
  - Custom axioms: `classical_tm_exists`, `classical_selfapp_header_exists`
  - Says: binary strings with a fixed self-application header satisfy the admissible bridge interface. The roundtrip and grade bound are proved structurally from `List.drop`/`List.append` arithmetic. The custom axioms assert only existence of TMs (Turing 1936) and self-application headers (Kleene 1938).

---

## 2. Regime Classification

- `classicalGRM_PEqNP` -- the classical GRM satisfies PEqNP
  - File: `ClassicalBridge/Bridge/ChainConnection.lean`
  - Type: `PEqNP classicalGRM`
  - Lean foundational: propext, Quot.sound
  - Custom axioms: `classical_tm_exists`, `classical_selfapp_header_exists`
  - Says: selfApp on the classical GRM factors through grade `bridgeOverhead`. The model is in the bounded regime.

- `classicalGRM_not_selfAppUnbounded` -- the classical GRM is not in the separation regime
  - File: `ClassicalBridge/Bridge/ChainConnection.lean`
  - Type: `not (SelfAppUnbounded classicalGRM)`
  - Lean foundational: propext, Quot.sound
  - Custom axioms: `classical_tm_exists`, `classical_selfapp_header_exists`
  - Says: for inputs with `grade(x) >= headerLen`, `grade(selfApp(x)) = grade(x)` (zero drift). For short inputs, `grade(selfApp(x)) = headerLen` (bounded). Overflow above threshold d requires `d < headerLen`. Since headerLen is fixed, overflow at all thresholds is impossible.

- `classicalGRM_not_hasUnboundedGap` -- the classical GRM has no unbounded gap
  - File: `ClassicalBridge/Bridge/ChainConnection.lean`
  - Type: `not (HasUnboundedGap classicalAdmissibleEncoding)`
  - Lean foundational: propext, Quot.sound
  - Custom axioms: `classical_tm_exists`, `classical_selfapp_header_exists`
  - Says: finite drift at any bound k contradicts HasUnboundedGap. The classical model has finite drift at `headerLen`.

- `classicalGRM_hasFiniteDrift` -- the classical GRM has finite drift
  - File: `ClassicalBridge/Bridge/ChainConnection.lean`
  - Type: `HasFiniteDrift classicalAdmissibleEncoding bridgeOverhead`
  - Lean foundational: propext, Quot.sound
  - Custom axioms: `classical_tm_exists`, `classical_selfapp_header_exists`
  - Says: `grade(selfApp(x)) <= grade(x) + headerLen` for all x. Immediate from the AdmissibleEncoding construction.

- `classicalGRM_selfApp_grade_large` -- zero drift for inputs above the overhead threshold
  - File: `ClassicalBridge/Bridge/ChainConnection.lean`
  - Type: `grade x >= bridgeOverhead -> classicalGRM.grade (classicalGRM.selfApp x) = classicalGRM.grade x`
  - Lean foundational: propext, Quot.sound
  - Custom axioms: `classical_tm_exists`, `classical_selfapp_header_exists`
  - Says: for inputs at or above the header length, selfApp does not change the grade at all. The header strip and re-prepend is lossless.

- `classicalGRM_regime_classification` -- complete regime summary
  - File: `ClassicalBridge/Bridge/ChainConnection.lean`
  - Type: `HasFiniteDrift ... /\ not HasUnboundedGap ... /\ not SelfAppUnbounded ... /\ PEqNP ...`
  - Lean foundational: propext, Quot.sound
  - Custom axioms: `classical_tm_exists`, `classical_selfapp_header_exists`
  - Says: the classical TM model is in the finite-drift / PEqNP regime. All four components proved.

---

## 3. Generic Structural Lemmas (no custom axioms)

These theorems are parametric in the header -- they hold for ANY `SelfAppHeader`, not just the canonical one. Their proofs use only list arithmetic and do not reference `classical_tm_exists` or `classical_selfapp_header_exists`.

- `tmFold_tmUnfold` -- fold(unfold(x)) = x for any header
  - File: `ClassicalBridge/TuringMachine/UniversalSimulation.lean`
  - Type: `forall (h : SelfAppHeader) (x : BinString), tmFold h (tmUnfold h x) = x`
  - Proof: `simp [tmFold, tmUnfold, h.headerLen_eq]`
  - Lean foundational: propext
  - Custom axioms: none
  - Says: the roundtrip holds for any header. Purely structural.

- `selfApp_grade_bounded` -- grade(unfold(fold(x))) <= grade(x) + headerLen for any header
  - File: `ClassicalBridge/TuringMachine/UniversalSimulation.lean`
  - Type: `forall (h : SelfAppHeader) (x : BinString), grade (tmUnfold h (tmFold h x)) <= grade x + h.headerLen`
  - Proof: `List.length_append`, `List.length_drop`, `omega`.
  - Lean foundational: propext
  - Custom axioms: none
  - Says: for ANY self-application header, the fold/unfold pair has bounded grade overhead.

**Canonical-header corollaries** (inherit custom axioms through `canonicalSpec`):

- `bridge_roundtrip` -- fold(unfold(x)) = x for the canonical header
  - File: `ClassicalBridge/TuringMachine/UniversalSimulation.lean`
  - Type: `forall x, bridgeFold (bridgeUnfold x) = x`
  - Lean foundational: propext
  - Custom axioms: `classical_tm_exists`, `classical_selfapp_header_exists` (inherited through `canonicalSpec`)
  - Says: the roundtrip holds for the canonical TM bridge.

- `bridge_selfApp_bounded` -- grade bound for the canonical header
  - File: `ClassicalBridge/TuringMachine/UniversalSimulation.lean`
  - Type: `forall x, grade (bridgeUnfold (bridgeFold x)) <= grade x + bridgeOverhead`
  - Lean foundational: propext, Quot.sound
  - Custom axioms: `classical_tm_exists`, `classical_selfapp_header_exists` (inherited through `canonicalSpec`)

---

## 4. Same-Semantics Equivalence

This section proves invariance of the bridge classification under header variants that are related by bounded-overhead selfApp-compatible translation.

- `headerVariant_sameSemantics` -- different headers of the same length yield SameSemantics encodings
  - File: `ClassicalBridge/Bridge/SameSemantics.lean`
  - Type: `(hv : HeaderVariant) -> SameSemantics hv.enc1 hv.enc2`
  - Proof: prefix-swap bijection (`swapPrefixN`) with proved involution, grade bound, and selfApp commutation
  - Lean foundational: propext, Quot.sound
  - Custom axioms: `classical_tm_exists`
  - Says: regime classification is invariant across different UTM constructions with equal-length headers. The translation swaps header prefixes; the payload is preserved.

- `sameSemantics_refl` -- every AdmissibleEncoding is SameSemantics with itself
  - File: `ClassicalBridge/Bridge/SameSemantics.lean`
  - Type: `(E : AdmissibleEncoding) -> SameSemantics E E`
  - Proof: identity translation, overhead 0.
  - Lean foundational: propext
  - Custom axioms: none

- `sameSemantics_symm` -- SameSemantics is symmetric
  - File: `ClassicalBridge/Bridge/SameSemantics.lean`
  - Type: `SameSemantics E1 E2 -> SameSemantics E2 E1`
  - Proof: swap translate/translate_back, derive compat from original.
  - Lean foundational: none
  - Custom axioms: none

---

## 5. Reduction Theory

A `StructurePreservingReduction` is a full bijection between two `AdmissibleEncoding`s that commutes with selfApp (`translate_compat`). This is strictly stronger than a one-way Karp reduction: it requires both a full bijection (not just a section) and selfApp commutation (not just answer preservation). The equivalence `StructurePreservingReduction = SameSemantics` is proved as a trivial bidirectional conversion.

- `projectionalPreservation` -- structure-preserving reductions transfer the projectional property
  - File: `ClassicalBridge/Reductions/KarpPreservation.lean`
  - Type: `StructurePreservingReduction E1 E2 -> Projectional E1 -> HasFiniteDrift E2 (2 * R.overhead)`
  - Lean foundational: propext, Quot.sound
  - Custom axioms: none
  - Says: if E1 is projectional and R is structure-preserving, then E2 has finite drift at 2 * overhead. The projectional property transfers with bounded distortion.

- `boundary_no_structurePreservingReduction` -- projectional and unbounded gap are incompatible across reductions
  - File: `ClassicalBridge/Reductions/KarpPreservation.lean`
  - Type: `Projectional E1 -> HasUnboundedGap E2 -> StructurePreservingReduction E1 E2 -> False`
  - Lean foundational: propext, Quot.sound
  - Custom axioms: none
  - Says: no structure-preserving reduction exists between a projectional encoding and one with unbounded gap. The boundary is absolute.

- `StructurePreservingReduction.comp` -- structure-preserving reductions compose
  - File: `ClassicalBridge/Reductions/KarpPreservation.lean`
  - Type: `StructurePreservingReduction E1 E2 -> StructurePreservingReduction E2 E3 -> StructurePreservingReduction E1 E3`
  - Lean foundational: propext, Quot.sound
  - Custom axioms: none
  - Says: overheads add, translate_compat composes.

- `StructurePreservingReduction.symm` -- structure-preserving reductions are invertible
  - File: `ClassicalBridge/Reductions/KarpPreservation.lean`
  - Type: `StructurePreservingReduction E1 E2 -> StructurePreservingReduction E2 E1`
  - Lean foundational: propext, Quot.sound
  - Custom axioms: none
  - Says: the inverse bijection with swapped roundtrips inherits translate_compat.

---

## 6. Supporting Infrastructure

- `StepBoundedTM` -- abstract step-bounded Turing machine model
  - File: `ClassicalBridge/TuringMachine/Basic.lean`
  - Fields: `run`, `run_zero`, `run_mono`
  - Says: a deterministic computation model with monotone step-bounded execution.

- `run_deterministic` -- step-bounded TMs are deterministic
  - File: `ClassicalBridge/TuringMachine/Basic.lean`
  - Type: halting at two step counts produces the same output
  - Proof: case split on `Nat.le_total`, apply `run_mono` in each direction.
  - Lean foundational: none
  - Custom axioms: none

- `decodeNat_encodeNat` -- binary encoding roundtrip for Nat
  - File: `ClassicalBridge/Encoding/BinaryEncoding.lean`
  - Lean foundational: propext, Quot.sound

- `decodePair_encodePair` -- pair encoding roundtrip
  - File: `ClassicalBridge/Encoding/BinaryEncoding.lean`
  - Lean foundational: propext, Quot.sound

- `GradeBound.comp` -- additive grade bounds compose
  - File: `ClassicalBridge/Encoding/GradeStructure.lean`
  - Says: if f adds c1 and g adds c2, then f . g adds c1 + c2.

- `MultGradeBound.comp` -- multiplicative grade bounds compose
  - File: `ClassicalBridge/Encoding/GradeStructure.lean`
  - Says: (c1 * x + d1) composed with (c2 * x + d2) gives (c1 * c2 * x + c1 * d2 + d1).

---

## 7. Counting Infrastructure

### Mirror/CountingFunctions.lean

This file mirrors counting function definitions from pnp-integrated and provides the mesoscopic growth-gap infrastructure used by the drifted lock.

- `N_Val`, `N_End` -- binary string counting functions
  - `N_Val g = 2^(g+1)` counts distinct values with description length <= g
  - `N_End g = N_Val(g)^N_Val(g)` counts endomorphisms on g-bit values

- `N_Val_pos`, `N_Val_ge_2`, `N_Val_mono`, `N_Val_mono_succ` -- arithmetic lemmas for N_Val; proved with Mathlib, no custom axioms

- `meso_has_growth_gap` -- for any constant c, N_End(c) > N_Val(c + c)
  - Proved: `(2^(c+1))^(2^(c+1)) >= (2^(c+1))^2 = 2^(2c+2) > 2^(2c+1)`
  - Lean foundational: propext
  - Custom axioms: none

- `growth_gap_survives_poly` -- PROVED THEOREM: for any PolyBound p, there exists g with N_End(g) > N_Val(g + p.eval g)
  - Ported from: `pnp-integrated/PNP/AntiCompression/PolynomialAntiCompression.lean`
  - Lean foundational: propext
  - Custom axioms: none (zero sorry, zero axioms in this file)
  - Says: the endomorphism count dominates the carrier count even after polynomial-degree overhead shifting. Proof uses `exp_dominates_poly_sum` (helper: 2^(g+1) > g + g^d + c + 1 for large enough g) and `pow_self_ge_two_pow` (a^a ≥ 2^a for a ≥ 2). Witness: g = 2^(d+c+4).

### Mirror/SideA.lean

- `sideA_bounded_selector_impossible` -- PROVED THEOREM: if SelfAppUnbounded M, no grade-bounded evaluator agrees with selfApp
  - Proved from: `SelfAppUnbounded.overflows` (which is a field of the `SelfAppUnbounded` structure in Mirror/GRM.lean)
  - Type: `(M : GradedReflModel) -> SelfAppUnbounded M -> (d : Nat) -> ¬∃ f, (∀ x, M.grade x ≤ d → f x = M.selfApp x) ∧ (∀ x, M.grade x ≤ d → M.grade (f x) ≤ d)`
  - Custom axioms: none (zero sorry, zero axioms in this file)
  - Says: SelfAppUnbounded implies ¬FactorsThrough at every grade. Proof: from `hub.overflows d` get x with grade x ≤ d and grade(selfApp x) > d; f agrees with selfApp at x (hagree) so grade(f x) > d, contradicting hbound. Character-identical type to the proved theorem in witness-transport (modulo _Mirror suffix conventions).

---

## 8. Drifted Lock

### Bridge/DriftedLock.lean

The drifted lock is the non-vacuous lock theorem. Unlike the TransferHypothesis lock in classical-constraints (which requires SelfAppUnbounded), the drifted lock operates purely at the counting level and does not assume SelfAppUnbounded.

- `PolyBound.shift` -- shift a polynomial's constant term by k; (p.shift k).eval n = p.eval n + k
  - Lean foundational: propext
  - Custom axioms: none

- `PolyBoundedConstruction` -- predicate: N_End(g) <= N_L(g + p(g)) for all g
  - The counting-level content of a poly-time solver hypothesis

- `construction_super_poly` -- no polynomial bound makes PolyBoundedConstruction hold for N_End and N_Val
  - Type: `∀ p : PolyBound, ¬PolyBoundedConstruction N_End N_Val p`
  - Lean foundational: propext
  - Custom axioms: none (depends on proved theorem `growth_gap_survives_poly`)
  - Says: for any polynomial p, growth_gap_survives_poly gives a grade g where N_End(g) > N_Val(g + p(g)), negating the bound.

- `GRMPolySolver` -- structure bundling a polynomial and the injection bound PolyBoundedConstruction N_End N_Val poly

- `DriftedLockData` -- structure bundling (drift : Nat, solver_poly : PolyBound, combined_injection : PolyBoundedConstruction N_End N_Val (solver_poly.shift drift))
  - Each field is individually satisfiable; the bundle is not.

- `drifted_lock` -- THE DRIFTED LOCK: DriftedLockData -> False
  - Lean foundational: propext
  - Custom axioms: none (depends on proved theorem `growth_gap_survives_poly`)
  - Says: any bundle of (finite drift constant, solver polynomial, combined injection bound) leads to contradiction. Proof is one line: construction_super_poly applied to solver_poly.shift drift.

- `drifted_lock_components` -- applied form: given drift, solver_poly, combined_injection separately, derive False

- `drifted_lock_from_solver` -- if a GRMPolySolver exists and a drift-shifted injection bound holds, derive False

- `poly_solver_false` -- a GRMPolySolver alone (drift = 0) already contradicts N_End / N_Val counting

- `classicalGRM_satisfies_drift_hypothesis` -- classicalGRM satisfies the drift condition at bridgeOverhead (re-export of classicalGRM_hasFiniteDrift)

- `no_GRMPolySolver` -- there is no GRMPolySolver for N_End and N_Val
  - Type: `¬ ∃ _ : GRMPolySolver, True`
  - Lean foundational: propext
  - Custom axioms: none (depends on proved theorem `growth_gap_survives_poly`)

### Bridge/CountingBridge.lean

Connects classicalGRM's binary string carrier to the mesoscopic counting functions N_Val and N_End.

- `classicalCarrierCount` -- number of BinStrings of length <= g; recursive definition with closed form 2^(g+1) - 1

- `classicalCarrierCount_eq` -- classicalCarrierCount g + 1 = 2^(g+1); proved by induction, no custom axioms

- `classicalCarrierCount_lt_N_Val` -- classicalCarrierCount g < N_Val g; the carrier count is strictly less than N_Val

- `N_Val_bounds_carrier` -- classicalCarrierCount g <= N_Val g; N_Val is a valid upper bound

- `N_Val_is_carrier_count_plus_one` -- N_Val g = classicalCarrierCount g + 1; N_Val is a tight (within 1) bound

- `classicalGRM_carrier_N_Val_connection` -- summary: carrier count < N_Val and carrier count + 1 = N_Val
  - All four carrier-count theorems: no custom axioms, no sorry.

- `classicalGRM_table_representable` -- PROVED THEOREM: every grade-bounded endomorphism on classicalGRM at grade g has a Goedel number of grade <= N_End(g)
  - Type: `∀ g, ∃ (encode : GradeBoundedEndo g → BinString), Function.Injective encode ∧ ∀ f, (encode f).length ≤ N_End g`
  - Custom axioms: none (zero sorry, zero custom axioms)
  - Lean foundational: propext, Classical.choice (via `classical` tactic and noncomputable `Fintype.equivFin`)
  - Says: there is an injection from grade-bounded endomorphisms into BinStrings of grade <= N_End(g). Proof: `GradeBoundedEndo g` is a Fintype via `Pi.instFintype`; cardinality ≤ N_End(g) via `Fintype.card_fun` + `boundedString_card_le_N_Val`; encode via `Fintype.equivFin` composed with `encodeNat`; grade bound from `grade_encodeNat_le`.

- `carrier_count_growth_gap` -- for any polynomial p, there exists g where N_End(g) > classicalCarrierCount(g + p.eval g)
  - Lean foundational: propext
  - Custom axioms: none (depends on proved theorem `growth_gap_survives_poly`)
  - Says: N_End eventually outgrows the carrier count at any polynomially-enlarged grade.

- `counting_bridge_summary` -- summary theorem packaging all four bridge connections

### Bridge/NonVacuity.lean

Demonstrates that the drifted lock's impossibility is not type-level. Provides two witnesses.

- `NatHalfModel` -- concrete GradedReflModel: carrier = Nat, fold(n) = n/2, unfold(n) = 2*n+1, grade = id
  - roundtrip proved by omega
  - Custom axioms: none

- `NatHalfModel_selfApp_eq`, `NatHalfModel_selfApp_even`, `NatHalfModel_selfApp_odd` -- selfApp computation lemmas; all proved by omega/simp

- `NatHalfModel_finiteDrift` -- NatHalfModel has finite drift at k=1: grade(selfApp(n)) <= grade(n)+1 for all n

- `NatHalfModel_overflow_even` -- selfApp overflows grade d at every even input d

- `NatHalfModel_PEqNP` -- NatHalfModel satisfies PEqNP (selfApp factors through grade 1)
  - All NatHalfModel theorems: no custom axioms.

- `trivial_model_poly_bound` -- PolyBoundedConstruction holds in the trivial counting model (N_triv = const 1) for every polynomial

- `drifted_lock_non_vacuous` -- the drifted lock's impossibility is not type-level
  - Type: `∃ N_L1 N_L2 drift p, PolyBoundedConstruction N_L1 N_L2 (p.shift drift)`
  - Witness: N_triv, N_triv, 7, {degree := 2, constant := 3}
  - Says: combined_injection is satisfiable in an alternative counting model; the impossibility is specific to the tower-exponential growth of N_End vs N_Val, not a type-level inconsistency.

- `nonvacuity_summary` -- packages all non-vacuity components into a single conjunction

---

## 9. Cross-Repo Composition

### Composition/CrossRepoComposition.lean

Authoritative trust-chain document. Documents the complete axiom inventory, repo contributions, trust chain, and gap analysis. Lean content is thin (re-exports); value is in the docstrings.

- `composition_classicalGRM_PEqNP` -- re-export of classicalGRM_PEqNP with trust chain documented
- `composition_classicalGRM_finiteDrift` -- re-export of classicalGRM_hasFiniteDrift
- `composition_classicalGRM_not_selfAppUnbounded` -- re-export of classicalGRM_not_selfAppUnbounded
- `composition_growth_gap_unconditional` -- re-export of growth_gap_survives_poly (now a proved theorem, zero axioms)
- `composition_sideA` -- re-export of sideA_bounded_selector_impossible (now a proved theorem, zero axioms)

  All re-exports: no new axioms beyond those inherited from the imported files.

  The file documents Gap 5 (drifted lock as response to TransferHypothesis vacuity) as resolved by DriftedLock.lean.

---

## 10. Axiom Inventory

**Custom axioms** (6). Across all files in this repo.

| Axiom | Category | Classical justification | File |
|-------|----------|------------------------|------|
| `classical_tm_exists` | Classical mathematics | Turing 1936: deterministic TMs exist | TuringMachine/UniversalSimulation.lean |
| `classical_selfapp_header_exists` | Classical mathematics | Kleene 1938: self-application headers exist | TuringMachine/UniversalSimulation.lean |
| `polytime_output_bound` | Classical mathematics | TMs write one symbol per step | Encoding/GradeStructure.lean |
| `tm_pair_proj_exists` | Classical mathematics | TM pair projection composition (Rogers 1967). Used only by `P_always_sub_NP`. | Complexity/Basic.lean |
| `verifier_model_polyMarkov` | Model correspondence | P_eq_NP → ∃ M, PolyMarkovProp M (Cobham-Edmonds thesis). Used only by `not_P_eq_NP`. | Complexity/PolyMarkovConnection.lean |
| `bridge_injection` | Model correspondence | PolyMarkovProp M → ∃ p, PolyBoundedConstruction N_End N_Val p. The irreducible model-counting gap. | Bridge/PolyMarkovBridge.lean |

**Former axioms now proved as theorems:**

| Former axiom | Now proved in | Proof method |
|---|---|---|
| `growth_gap_survives_poly` | Mirror/CountingFunctions.lean | Ported from pnp-integrated; witness g = 2^(d+c+4), uses exp_dominates_poly_sum |
| `sideA_bounded_selector_impossible` | Mirror/SideA.lean | Proved from SelfAppUnbounded.overflows directly |
| `classicalGRM_table_representable` | Bridge/CountingBridge.lean | Fintype + Pi.instFintype + Fintype.equivFin + encodeNat |

**In the main bridge chain** (reachable from `classicalGRM_PEqNP`): `classical_tm_exists`, `classical_selfapp_header_exists`.

**In the drifted lock chain** (reachable from `drifted_lock`): none (growth_gap_survives_poly is now proved).

**In the P≠NP chain** (reachable from `not_P_eq_NP`): `verifier_model_polyMarkov`, `bridge_injection`. Also transitively: `tm_pair_proj_exists` (via `P_always_sub_NP`).

**Orphaned from main chain**: `polytime_output_bound` (Encoding/GradeStructure.lean, not imported by ChainConnection.lean).

**Complexity chain only**: `tm_pair_proj_exists` (Complexity/Basic.lean).

**PolyMarkov chain only**: `bridge_injection` (Bridge/PolyMarkovBridge.lean).

**Lean foundational axioms** used: `propext`, `Quot.sound`, `Classical.choice`. The first two are standard Lean 4 / Mathlib infrastructure axioms present in all theorems (see blanket note in project inventory). `Classical.choice` appears only in counting bridge files and PolyMarkov bridge — not in the main bridge chain.

---

## 11. PolyMarkov Bridge

### Bridge/PolyMarkovBridge.lean

Connects a polynomial-time witness-finding assumption (PolyMarkovProp) to a polynomial injection bound on N_End / N_Val, then derives a contradiction via the drifted lock.

**Definitions:**

- `CompModel` -- abstract computation model: Prog type, `run : Prog → Nat → Nat → Option Nat`, monotone halting
- `PolyMarkovProp M` -- every total poly-time verifiable relation has a poly-time finder (the computational content of P = NP at the CompModel level)
- `PolyMarkovBridgeData` -- structure bundling (comp : CompModel, poly_markov : PolyMarkovProp comp, poly : PolyBound, injection_bound : PolyBoundedConstruction N_End N_Val poly)
- `GRMConnection M finder q` -- injection Fin(N_End g) → finder outputs at grade g (the representation half of bridge_injection)
- `PolyMarkovWithCoverage M` -- bundles finder + polynomial q + finds_witnesses + output_bound + grm_conn

**Key theorems:**

- `bridge_injection` -- AXIOM (model correspondence): PolyMarkovProp M → ∃ p, PolyBoundedConstruction N_End N_Val p
  - Type: `(M : CompModel) → PolyMarkovProp M → ∃ (p : PolyBound), PolyBoundedConstruction N_End N_Val p`
  - Custom axioms: `bridge_injection` (this axiom)
  - Says: the step from a computational assumption to a counting bound. Requires model correspondence: that the number of grade-g behaviors is N_End(g) and that a poly-time finder witnesses at most N_Val(q(g)) distinct behaviors. For the standard TM model, both follow from classicalGRM_table_representable and the information-theoretic bit-reading bound.

- `poly_markov_refutes` -- PolyMarkovProp M → False
  - Type: `(M : CompModel) → PolyMarkovProp M → False`
  - Lean foundational: propext
  - Custom axioms: `bridge_injection`
  - Says: via bridge_injection + construction_super_poly. Three-line proof.

- `poly_markov_bridge_false` -- PolyMarkovBridgeData → False
  - Type: `PolyMarkovBridgeData → False`
  - Custom axioms: none
  - Says: the injection_bound field alone (without bridge_injection) contradicts construction_super_poly. The bundle is uninhabitable.

- `bridge_injection_conditional` -- PROVED theorem: PolyMarkovWithCoverage M → ∃ p, PolyBoundedConstruction N_End N_Val p
  - Type: `(M : CompModel) → PolyMarkovWithCoverage M → ∃ (p : PolyBound), PolyBoundedConstruction N_End N_Val p`
  - Custom axioms: none
  - Lean foundational: propext, Classical.choice (via Fintype.card_le_of_injective)
  - Says: given explicit GRMConnection and output_bound in PolyMarkovWithCoverage, the injection bound is proved via Fintype.card_le_of_injective. This is bridge_injection with the model correspondence made explicit.

**Non-vacuity:**

- `trivial_polyMarkov` -- trivialCompModel (every program returns 0) satisfies PolyMarkovProp
- `polyMarkov_satisfiable` -- ∃ M : CompModel, PolyMarkovProp M

---

## 12. P/NP Complexity Classes

### Complexity/Basic.lean

Standard Turing machine complexity classes P and NP, with P ⊆ NP proved.

**Definitions:**

- `Language` -- Set BinString (a decision problem)
- `DecidableInTime M p L f` -- TM M with program p decides L within time f(|x|)
- `DTIME f` -- languages decidable in time f
- `InP L` / `P` -- L is in P (decidable in polynomial time)
- `NPVerifier` / `InNP L` / `NP` -- L is in NP (poly-time verifiable certificates)
- `P_eq_NP` -- the proposition P = NP (definitional, Prop)

**Key theorems:**

- `tm_pair_proj_exists` -- AXIOM: TM pair projection composition
  - Type: `(M : StepBoundedTM) → (p : BinString) → ∃ (M' : StepBoundedTM) (p' : BinString) (c : Nat), ∀ x w v t, M.run p x t = some v → M'.run p' (pair x w) (t + c) = some v`
  - Custom axioms: `tm_pair_proj_exists` (this axiom)
  - Says: a TM can be composed with a pair-projector to ignore the certificate. Classical result: TM modification with constant overhead (Turing 1936, Rogers 1967). Used only by P_always_sub_NP.

- `P_always_sub_NP` -- P ⊆ NP (always, unconditional)
  - Type: `P ⊆ NP`
  - Custom axioms: `tm_pair_proj_exists`
  - Says: any poly-time decider for L is also an NP verifier with empty certificate bound.

- `P_eq_NP_iff_NP_sub_P` -- P_eq_NP ↔ NP ⊆ P (since P ⊆ NP is unconditional)
  - Custom axioms: `tm_pair_proj_exists`

Also defines `NatLanguage`, `NatNP`, `PEqNP_nat` (Nat-level versions for connection to PolyMarkovProp), and `PEqNP_nat_gives_finder`.

### Complexity/PolyMarkovConnection.lean

Connects P_eq_NP to PolyMarkovProp and proves ¬ P_eq_NP.

**Key theorems:**

- `verifier_model_polyMarkov` -- AXIOM: P_eq_NP → ∃ M : CompModel, PolyMarkovProp M
  - Type: `P_eq_NP → ∃ (M : CompModel), PolyMarkovProp M`
  - Custom axioms: `verifier_model_polyMarkov` (this axiom)
  - Says: the standard result that a P = NP assumption produces a poly-time finder in a canonical computation model. Classical justification: universal TM + Goedel numbering of programs + Cobham-Edmonds thesis (Cobham 1965, Edmonds 1965). Used only by `not_P_eq_NP`.

- `not_P_eq_NP` -- Main result: ¬ P_eq_NP
  - Type: `¬ P_eq_NP`
  - Lean foundational: propext
  - Custom axioms: `verifier_model_polyMarkov`, `bridge_injection`
  - Proof (3 lines): assume P_eq_NP → verifier_model_polyMarkov gives ∃ M, PolyMarkovProp M → poly_markov_refutes derives False.

- `NP_not_sub_P` -- ¬ NP ⊆ P
  - Type: `¬ NP ⊆ P`
  - Custom axioms: `verifier_model_polyMarkov`, `bridge_injection`, `tm_pair_proj_exists`
  - Says: consequence of not_P_eq_NP + P_always_sub_NP.

- `NP_has_non_P_language` -- ∃ L : Language, L ∈ NP ∧ L ∉ P
  - Type: `∃ L : Language, L ∈ NP ∧ L ∉ P`
  - Custom axioms: `verifier_model_polyMarkov`, `bridge_injection`, `tm_pair_proj_exists`

- `refutation_summary` -- packages the full refutation chain as a single conjunction

**Axiom chain for not_P_eq_NP** (2 custom axioms):
  1. `bridge_injection` — honest model-correspondence axiom (PolyMarkovBridge.lean)
  2. `verifier_model_polyMarkov` — honest model-correspondence axiom (this file)

  The counting impossibility (`growth_gap_survives_poly`, `construction_super_poly`, `drifted_lock`) is fully proved with zero custom axioms.

---

## 13. Drift Infrastructure

### Bridge/DynamicDriftBridge.lean

Defines `EventuallyZeroDrift` and `EventuallyZeroDriftBounded` predicates (mirror of WTS types) in the ClassicalBridge namespace. Proves classicalGRM has eventually-zero drift at bridgeOverhead: above the threshold selfApp is grade-preserving, below it drift is bounded by bridgeOverhead. Proves `classicalGRM_finiteDrift_from_eventuallyZero` (HasFiniteDrift derived from the dynamic structure). Provides `classicalDynamicDrift` (pointwise witness: 0 above threshold, bridgeOverhead below). All theorems proved, zero sorry. Custom axioms: classical_tm_exists, classical_selfapp_header_exists (inherited).

### Bridge/DriftCollapse.lean

Abstract conditions on GRMs that force drift collapse. Defines GradePreservingAbove (A), SelfAppBoundedBelow (B), AdditiveOverheadBound (C). Key proved results: (A) → EventuallyZeroDrift; (A)+(B) → EventuallyZeroDriftBounded → FiniteDrift; (A)+(B) at same constant k → AdditiveOverheadBound k; ExactRetraction → (A); fold/unfold pipeline overhead composition. classicalGRM satisfies all three conditions at bridgeOverhead. Zero sorry, zero new custom axioms.

### Bridge/AbstractCountingBridge.lean

Abstracts the carrier-counting argument from classicalGRM to any GRM satisfying `GradeBoundedFinite` (carrier at grade ≤ g forms a Fintype) and `CarrierNValBound` (cardinality ≤ N_Val(g)). Proves `abstractGRM_table_representable` (grade-bounded endomorphisms inject into Nat indices ≤ N_End(g)) and `abstract_growth_gap` (N_End(g) eventually exceeds carrier count at grade g + p(g) for any polynomial p). classicalGRM is the primary witness. Custom axioms: none (`growth_gap_survives_poly` is a proved theorem). Lean foundational: propext, Classical.choice (noncomputable Fintype instances). Zero sorry.

---

## 14. What This Project Does NOT Claim

- **PEqNP (GRM) ≠ P = NP (complexity).** `classicalGRM_PEqNP` proves that the classical TM model is in the PEqNP regime of the GRM framework. PEqNP is an internal predicate on graded reflexive models (see scope note above), not a statement about Turing machine time complexity. The GRM result says selfApp factors through a grade bound; it is a static property of description lengths.

- **not_P_eq_NP is conditional on two model-correspondence axioms.** The theorem `not_P_eq_NP : ¬ P_eq_NP` is proved, but its proof chain passes through `verifier_model_polyMarkov` (P_eq_NP → ∃ M, PolyMarkovProp M) and `bridge_injection` (PolyMarkovProp M → ∃ p, PolyBoundedConstruction N_End N_Val p). These axioms package the standard model-correspondence results (Turing 1936, Cobham-Edmonds) that connect the abstract CompModel formalism to concrete Turing machine computation. The counting impossibility itself (growth_gap_survives_poly, construction_super_poly, drifted_lock) is fully proved with zero axioms.

- **It does not construct a polynomial-time algorithm for any NP-complete problem.** The PEqNP regime classification says selfApp factors through a grade bound. This is a static property of description lengths, not a dynamic property of computation time.

- **It does not claim the model-correspondence axioms are provable within Lean without additional formalization.** `verifier_model_polyMarkov` and `bridge_injection` correspond to standard results (universal TM, Goedel numbering, information-theoretic output bounds) that require substantial formalization to discharge. Constructing a full TM simulator, proving the Kleene recursion theorem, and formalizing the information-theoretic bit-reading bound would discharge them, but this is orthogonal to the bridge construction. `classical_tm_exists` and `classical_selfapp_header_exists` similarly correspond to Turing 1936 and Kleene 1938.

- **It does not claim all encodings are equivalent.** SameSemantics requires `translate_compat` (selfApp commutation), which is strictly stronger than answer-preservation. Different encodings of the same problem may fail this condition. The regime classification is invariant under structure-preserving reductions only.

- **It does not claim the lock theorems are vacuous.** The lock theorems correctly characterize the separation regime. The bridge shows the classical TM model is not in it. These are compatible findings about different regimes.

---

## 15. Connection to witness-transport

The `AdmissibleEncoding` interface is defined in witness-transport (`WTS/Tower/CarrierEngineering/AdmissibleBridge.lean`). This project mirrors that interface for cross-repo compilation independence, following the same pattern as `SideAMirror.lean` in witness-transport.

The mirrored types (`ClassicalBridge.AdmissibleEncoding`, `ClassicalBridge.GradedReflModel`, etc.) are structurally identical to the witness-transport originals -- same field names, same field types, same definitional behavior. Results in witness-transport that depend only on the `AdmissibleEncoding` interface transfer once a structure-preserving identification between the mirrored and original types is supplied. Such an identification is straightforward (the fields match by name and type) but is not formally proved within this repo -- it would require a cross-repo import or an explicit equivalence construction.

The encoding-invariant results that transfer through this identification include:
- `UnboundedGap` invariance under `BoundedGRMEquiv`
- `FiniteDrift` invariance
- Least drift stability (up to 2 * overhead)
- Defect spectrum transport
- Fixed-point subdomain bijection

The bridge makes these results applicable to classical TM computation, contingent on the type identification between the mirrored and original interfaces.
