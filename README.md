[![Lean Action CI](https://github.com/LarsenClose/classical-bridge/actions/workflows/ci.yml/badge.svg)](https://github.com/LarsenClose/classical-bridge/actions/workflows/ci.yml)
[![Documentation](https://img.shields.io/badge/docs-GitHub%20Pages-blue)](https://larsenclose.github.io/classical-bridge/)

# classical-bridge

Constructs a concrete graded reflexive model from classical Turing machine computation and classifies its regime. Contains the headline results: `classicalGRM` (carrier = binary strings, selfApp = strip-and-reattach the Kleene self-application header, grade = string length), the counting engine (`construction_super_poly`, `drifted_lock`), P and NP as complexity classes over binary strings, and `not_P_eq_NP`. 22 Lean files, zero sorry.

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

This repo mirrors `GradedReflModel` and related types from witness-transport in the `Mirror/` directory. The repos cannot share imports; mirroring is for build isolation.

## Custom axioms

Six custom axioms, of which two are classical mathematics, one is orphaned, and three encode the standard computational interface:

- `classical_tm_exists` (Turing 1936): deterministic Turing machines exist.
- `classical_selfapp_header_exists` (Kleene 1938): a fixed self-application header exists via the recursion theorem.
- `polytime_output_bound`: basic TM property (t steps write at most t symbols). **Orphaned** -- not reachable from any main result. Retained for completeness.
- `tm_pair_proj_exists`: TM pairs project. Used by `P_always_sub_NP`.
- `verifier_model_polyMarkov`: P=NP implies polynomial-time finders exist. Definitional -- encodes what P=NP means computationally.
- `bridge_injection`: polynomial-time finders respect counting bounds. Definitional -- encodes what bounded computation does.

Three former axioms are now proved theorems: `growth_gap_survives_poly`, `sideA_bounded_selector_impossible`, `classicalGRM_table_representable`.

## Cross-repo notes

The `sideA` theorem is proved here independently in `Mirror/SideA.lean` (4 lines from `SelfAppUnbounded.overflows`). The same result is proved in pnp-integrated and mirrored as an axiom in classical-constraints.

## Theorem inventory

See `CLAIMS.md` for the complete theorem inventory with machine-verified axiom profiles.
