/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Mirror/SideA.lean — Side A impossibility theorem.

The Side A impossibility: if selfApp is unbounded, no grade-bounded evaluator
exists. No function can simultaneously agree with selfApp on grade-bounded
inputs and have grade-bounded outputs on those inputs.

Originally mirrored as an axiom from witness-transport, now proved directly
from SelfAppUnbounded.overflows (4-line proof). The proof is self-contained:
extract overflow witness, apply agreement + bound, derive contradiction.

The same result is proved independently in:
  - pnp-integrated/PNP/Transport/TransportCollapseObstruction.lean
  - witness-transport/WTS/Transport/TransportCollapseObstruction.lean
and mirrored as an axiom in:
  - classical-constraints/ClassicalConstraints/Shared/SideAMirror.lean

Note: classical-bridge uses GradedReflModel / SelfAppUnbounded (no _Mirror suffix),
while classical-constraints uses GradedReflModel_Mirror / SelfAppUnbounded_Mirror.
The type structures are identical; only the names differ.

STATUS: 0 sorry.
-/

import ClassicalBridge.Mirror.GRM

namespace ClassicalBridge

-- ════════════════════════════════════════════════════════════
-- Side A theorem (proved directly from SelfAppUnbounded.overflows)
-- ════════════════════════════════════════════════════════════

/-- Mirror of sideA_bounded_selector_impossible from
    WTS/Transport/TransportCollapseObstruction.lean
    (proved as a consequence of selfApp_not_factors).

    If selfApp is unbounded, no grade-bounded evaluator exists:
    there is no function that agrees with selfApp on grade-bounded
    inputs and has grade-bounded outputs on those inputs.

    Equivalent to ¬FactorsThrough M selfApp d, since any such f
    would witness factoring via f(x) = selfApp(x) on the bounded domain.

    Type signature is character-identical (modulo _Mirror suffix) to:
    - ClassicalConstraints.sideA_bounded_selector_impossible
      in classical-constraints/ClassicalConstraints/Shared/SideAMirror.lean
    - WTS.sideA_bounded_selector_impossible_mirror
      in witness-transport/WTS/Shared/SideAMirror.lean -/
theorem sideA_bounded_selector_impossible (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (d : Nat) :
    ¬∃ (f : M.carrier → M.carrier),
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) ∧
      (∀ x, M.grade x ≤ d → M.grade (f x) ≤ d) := by
  intro ⟨f, hagree, hbound⟩
  obtain ⟨x, hle, hgt⟩ := hub.overflows d
  have heq : f x = M.selfApp x := hagree x hle
  have hfx : M.grade (f x) ≤ d := hbound x hle
  rw [heq] at hfx
  omega

end ClassicalBridge
