# CLAIMS.md — classical-bridge

What this project proves, what it assumes, and what it does not claim.
Generated from the codebase on 2026-03-20. Every theorem name, file path,
and axiom profile is machine-verified via `#print axioms`.

> **Scope note.** `PEqNP` and `SelfAppUnbounded` are internal predicates on
> graded reflexive models (GRMs), defined in the carrier engineering framework
> of witness-transport. `PEqNP M` asserts that `selfApp` factors through some
> grade bound; `SelfAppUnbounded M` asserts no such bound exists. These are
> regime classifications within the GRM formalism. `SelfAppHeader` parameterizes
> the naming convention — it is a free parameter, not an axiom.

**Project status.** 28 source files. Zero sorry. Zero custom axioms in the
main theorem chain. Lean foundational axioms: `propext`, `Quot.sound`,
`Classical.choice` (standard Lean 4 / Mathlib foundations).

---

## 1. Primary Results

### naming_cost_nonclosure

- **File:** `ClassicalBridge/Complexity/SemanticBridge.lean`
- **Type:** `(h : SelfAppHeader) → (hne : h.headerLen > 0) → (φ : GRMorphism (transportGradedReflModel (classicalGRM_WTS h)) (classicalGRM_WTS h)) → False`
- **Lean foundational:** propext, Classical.choice, Quot.sound
- **Custom axioms:** none
- **Says:** for any naming convention with positive cost, no structure-preserving map exists from the transport tower T(classicalGRM h) back to classicalGRM h. The proof: GRMorphism commutation forces fold(φ(t)) = φ(t) and unfold(φ(t)) = φ(t). In classicalGRM, fold = List.drop headerLen (shortens) and unfold = header ++ · (lengthens by headerLen). No element can be fixed by both when headerLen > 0.

### classical_answer_space

- **File:** `ClassicalBridge/Complexity/SemanticBridge.lean`
- **Type:** `(h : SelfAppHeader) → ClassicalAnswerSpace h`
- **Lean foundational:** propext, Classical.choice, Quot.sound
- **Custom axioms:** none
- **Says:** for any naming convention h, inhabits the complete answer space: regime profile (MinimalNecessityGradient + transport tower), resource-indexed growth gap, no polynomial cover, and naming cost nonclosure when headerLen > 0.

### classical_computation_characterized

- **File:** `ClassicalBridge/Complexity/SemanticBridge.lean`
- **Type:** `(h : SelfAppHeader) → (hne : h.headerLen > 0) → (∀ x, grade(selfApp(x)) ≤ grade(x) + headerLen) ∧ (∀ φ : GRMorphism T(M) M, False) ∧ (∀ k, ¬∀ n, functionSpaceSize n ≤ nProg (n + k))`
- **Lean foundational:** propext, Classical.choice, Quot.sound
- **Custom axioms:** none
- **Says:** the three cannots as a single conjunction. (1) Irreducible naming cost. (2) Substrate structurally unreachable. (3) No polynomial covers the operational richness. Assembles `bridge_selfApp_bounded`, `naming_cost_nonclosure`, and `binary_no_uniform_bound`.

### fold_unfold_nonclosure

- **File:** `ClassicalBridge/Complexity/FoldUnfoldNonclosure.lean`
- **Type:** `(h : SelfAppHeader) → (hne : h.headerLen > 0) → (φ : FoldUnfoldSection T(classicalGRM h) (classicalGRM h)) → False`
- **Lean foundational:** propext, Classical.choice, Quot.sound
- **Custom axioms:** none
- **Says:** the fold/unfold asymmetry of classical naming blocks structural sections at the weakest level. `FoldUnfoldSection` requires only fold/unfold commutation — no grade condition. The contradiction arises purely from the length asymmetry: fold shortens by headerLen, unfold lengthens by headerLen. When headerLen > 0, no element can be fixed by both. Strengthens `naming_cost_nonclosure` (which requires the stronger GRMorphism) by weakening the hypothesis.

---

## 2. Regime Classification

| Theorem | File | Lean foundational | Custom axioms |
|---|---|---|---|
| `classicalGRM_PEqNP` | ChainConnection.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM_not_selfAppUnbounded` | ChainConnection.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM_not_hasUnboundedGap` | ChainConnection.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM_hasFiniteDrift` | ChainConnection.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM_factorsThrough` | ChainConnection.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM_regime_classification` | ChainConnection.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM_selfApp_grade_large` | ChainConnection.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM_selfApp_grade_small` | ChainConnection.lean | propext, Classical.choice, Quot.sound | none |

`classicalGRM_regime_classification` is the four-property conjunction: HasFiniteDrift ∧ ¬HasUnboundedGap ∧ ¬SelfAppUnbounded ∧ PEqNP.

---

## 3. General Framework (any M)

| Theorem | File | Lean foundational | Custom axioms |
|---|---|---|---|
| `regimeProfile` | SemanticBridge.lean | propext, Classical.choice, Quot.sound | none |
| `pairing_peqnp` | SemanticBridge.lean | none | none |
| `pairing_unbounded_absurd` | SemanticBridge.lean | none | none |

`RegimeProfile M` packages MinimalNecessityGradient M + transport properties (selfApp = id, PEqNP on T(M)). `regimeProfile M` inhabits this for any GRM. `pairing_peqnp` and `pairing_unbounded_absurd` are purely constructive (zero axioms).

---

## 4. Generic Structural Lemmas (parametric in h, no custom axioms)

| Theorem | File | Type | Lean foundational |
|---|---|---|---|
| `tmFold_tmUnfold` | UniversalSimulation.lean | `∀ h x, tmFold h (tmUnfold h x) = x` | propext |
| `selfApp_grade_bounded` | UniversalSimulation.lean | `∀ h x, grade(tmUnfold h (tmFold h x)) ≤ grade x + h.headerLen` | propext, Quot.sound |

---

## 5. Counting Infrastructure

| Theorem | File | Type (abbreviated) | Lean foundational | Custom axioms |
|---|---|---|---|---|
| `growth_gap_survives_poly` | CountingFunctions.lean | `∀ p, ∃ g, N_End g > N_Val (g + p.eval g)` | propext, Quot.sound | none |
| `sideA_bounded_selector_impossible` | SideA.lean | `SelfAppUnbounded M → ∀ d, ¬∃ f, agrees ∧ bounded` | propext, Quot.sound | none |
| `construction_super_poly` | DriftedLock.lean | `∀ p, ¬PolyBoundedConstruction N_End N_Val p` | propext, Quot.sound | none |
| `drifted_lock` | DriftedLock.lean | `DriftedLockData → False` | propext, Quot.sound | none |
| `meso_has_growth_gap` | CountingFunctions.lean | `∀ c, HasGrowthGap N_End N_Val c` | propext | none |

`growth_gap_survives_poly` is a proved theorem (ported from pnp-integrated). `sideA_bounded_selector_impossible` is proved from `SelfAppUnbounded.overflows` (4 lines).

---

## 6. Drift Infrastructure

| Theorem | File | Lean foundational | Custom axioms |
|---|---|---|---|
| `classicalGRM_eventuallyZeroDrift` | DynamicDriftBridge.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM_eventuallyZeroDriftBounded` | DynamicDriftBridge.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM_gradePreservingAbove` | DriftCollapse.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM_selfAppBoundedBelow` | DriftCollapse.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM_additiveOverheadBound` | DriftCollapse.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM_drift_collapse_summary` | DriftCollapse.lean | propext, Classical.choice, Quot.sound | none |

classicalGRM has eventually-zero drift: above bridgeOverhead, selfApp preserves grade exactly. Below, drift is bounded by bridgeOverhead.

---

## 7. Reduction Theory

| Theorem | File | Lean foundational | Custom axioms |
|---|---|---|---|
| `projectionalPreservation` | KarpPreservation.lean | propext, Quot.sound | none |
| `boundary_no_structurePreservingReduction` | KarpPreservation.lean | propext, Quot.sound | none |
| `StructurePreservingReduction.comp` | KarpPreservation.lean | propext, Quot.sound | none |
| `StructurePreservingReduction.symm` | KarpPreservation.lean | propext, Quot.sound | none |
| `projectional_implies_PEqNP` | KarpPreservation.lean | propext, Quot.sound | none |

`StructurePreservingReduction = SameSemantics` (bidirectional trivial conversion). No structure-preserving reduction connects projectional and unbounded-gap encodings.

---

## 8. Concrete TM Model

| Definition/Theorem | File | Lean foundational | Custom axioms |
|---|---|---|---|
| `classical_tm` | ConcreteModel.lean | propext, Classical.choice, Quot.sound | none |
| `classicalAdmissibleEncoding` | TMAdmissibleEncoding.lean | propext, Classical.choice, Quot.sound | none |
| `classicalGRM` | TMAdmissibleEncoding.lean | propext, Classical.choice, Quot.sound | none |

`classical_tm` wraps Mathlib's `Nat.Partrec.Code.evaln` with BinString encoding/decoding. `classicalAdmissibleEncoding h` assembles fold/unfold/roundtrip/grade/overhead from `SelfAppHeader h`. `classicalGRM h` is the induced GRM.

---

## 9. Former Architecture (Superseded)

| Former axiom/theorem | Status | Reason |
|---|---|---|
| `bridge_injection` | REMOVED | Unsound (proved False via trivialCompModel) |
| `verifier_model_polyMarkov` | REMOVED | Subsumed by DriftedPairing architecture |
| `not_P_eq_NP` via old chain | SUPERSEDED | Chain no longer exists |
| `classical_selfapp_header_exists` | SUPERSEDED | `SelfAppHeader` is now a parameter |
| `classical_tm_exists` | ELIMINATED | Proved as `classical_tm` in ConcreteModel.lean; shim removed |
| `carrier_P_eq_NP` / `not_carrier_P_eq_NP` | SUPERSEDED | Replaced by `fold_unfold_nonclosure` (positive structural framing) |
| `SelfAppHeaderProof.lean` | DELETED | Redundant with `emptySelfAppHeader` in UniversalSimulation.lean |

PolyMarkov bridge infrastructure remains in codebase as supporting material but is not part of the main theorem chain.

---

## 10. Cross-Repo Dependencies

| Repository | What is imported | Used by |
|---|---|---|
| witness-transport | `MinimalNecessityGradient`, `transportGradedReflModel`, `TransportSelfSimilarity`, `GRMorphism` | SemanticBridge.lean, ModelCorrespondence.lean |
| pnp-integrated | `ResourceSemantics` (`ResourceModel`, `binaryResourceModel`, `binary_growth_gap`, `binary_no_uniform_bound`) | SemanticBridge.lean |
| classical-constraints | Chain lock infrastructure | CrossRepoComposition.lean (documentation only) |

The main theorem chain (`naming_cost_nonclosure`, `classical_answer_space`, `classical_computation_characterized`) depends only on witness-transport and pnp-integrated.

---

## 11. Axiom Summary

**Custom axioms in main theorem chain:** 0

**Lean foundational axioms used:**
- `propext` — all theorems
- `Quot.sound` — most theorems
- `Classical.choice` — theorems involving classicalGRM (through Mathlib's computability library), MinimalNecessityGradient (through least drift extraction via Nat.find)

**Not used by main chain:** `Classical.choice` is NOT required by `pairing_peqnp`, `pairing_unbounded_absurd`, `growth_gap_survives_poly`, `sideA_bounded_selector_impossible`, `construction_super_poly`, `drifted_lock`, or any reduction theory theorem.
