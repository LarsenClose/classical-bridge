# classical-bridge

Constructs a concrete graded reflexive model from classical Turing machine computation and classifies its regime. Carrier = `BinString`, fold = `List.drop headerLen`, unfold = `header ++ ·`, grade = `List.length`. `SelfAppHeader` is a free parameter, not an axiom. 28 source files, zero sorry, zero custom axioms in the main theorem chain.

## Primary results

- `naming_cost_nonclosure` -- for any naming convention with positive cost, no GRMorphism maps from the transport tower back to classicalGRM.
- `fold_unfold_nonclosure` -- the fold/unfold asymmetry of classical naming blocks structural sections at the weakest level (FoldUnfoldSection, no grade condition). Strengthens naming_cost_nonclosure by weakening the hypothesis.
- `classical_answer_space` -- inhabits the complete answer space: regime profile, resource-indexed growth gap, no polynomial cover, and naming cost nonclosure.
- `classical_computation_characterized` -- the three cannots as a single conjunction: irreducible naming cost, structurally unreachable substrate, no polynomial cover.

## Build

```
lake build
```

Requires Lean 4.28.0 and Mathlib.

## Repository graph

```
witness-transport  (core definitions, carrier architecture, transport, invariance)
      |
pnp-integrated     (separation theorem, transport obstruction, anti-compression)
      |
classical-constraints  (seven chains, lock theorems, direct bridges)
      |
classical-bridge   <-- you are here
```

## Axiom profile

**Custom axioms in main theorem chain:** 0

**Lean foundational axioms:** `propext`, `Quot.sound`, `Classical.choice` (standard Lean 4 / Mathlib foundations).

`classical_tm` wraps Mathlib's `Nat.Partrec.Code.evaln` with BinString encoding/decoding -- no custom TM axiom. `SelfAppHeader` is a parameter, not an axiom. All former custom axioms (`classical_tm_exists`, `classical_selfapp_header_exists`, `tm_pair_proj_exists`, `bridge_injection`, `verifier_model_polyMarkov`) are proved, parameterized, or removed. One orphaned axiom (`polytime_output_bound`) remains, not reachable from any main result.

## Cross-repo dependencies

| Repository | What is imported | Used by |
|---|---|---|
| witness-transport | `MinimalNecessityGradient`, `transportGradedReflModel`, `GRMorphism` | SemanticBridge.lean, ModelCorrespondence.lean |
| pnp-integrated | `ResourceSemantics` (`ResourceModel`, `binary_growth_gap`, `binary_no_uniform_bound`) | SemanticBridge.lean |
| classical-constraints | Chain lock infrastructure | CrossRepoComposition.lean (documentation only) |

## Theorem inventory

See `CLAIMS.md` for the complete theorem inventory with machine-verified axiom profiles.
