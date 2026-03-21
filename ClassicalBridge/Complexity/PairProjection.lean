/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Complexity/PairProjection.lean — Proof of tm_pair_proj_exists.

Constructs a StepBoundedTM M' that, given a paired input pair(x, w), extracts
the first component x and simulates the original TM M on x. This eliminates
the axiom tm_pair_proj_exists from Complexity/Basic.lean by explicit construction.

## Strategy

1. Define `countLeadingFalse` to count leading false bits in a BinString.
2. Define `dropPrefix` to remove leading false bits and the true separator.
3. Define `extractFirst s = (dropPrefix s).take (countLeadingFalse s)`.
4. Prove `extractFirst (pair x w) = x` using induction on `x.length`.
5. Define M' with overhead c = 1:
     M'.run _ input steps = if steps ≥ 1 then M.run p (extractFirst input) (steps - 1) else none
6. Verify run_zero and run_mono for M'.
7. Conclude tm_pair_proj_exists_proved with M', p' = [], c = 1.

STATUS: 0 sorry.
-/

import ClassicalBridge.TuringMachine.Basic

namespace ClassicalBridge.Complexity.PairProjection

open ClassicalBridge.TM
open ClassicalBridge.Complexity

-- ════════════════════════════════════════════════════════════
-- Section 1: String decomposition helpers
-- ════════════════════════════════════════════════════════════

/-- Count the number of leading `false` bits in a BinString.
    Stops at the first `true` or at the end of the list. -/
def countLeadingFalse : BinString → Nat
  | []       => 0
  | true  :: _ => 0
  | false :: t  => countLeadingFalse t + 1

/-- Drop the leading `false` bits and the first `true` separator.
    If the string has no `true` bit, returns []. -/
def dropPrefix : BinString → BinString
  | []       => []
  | true  :: t => t
  | false :: t  => dropPrefix t

-- ════════════════════════════════════════════════════════════
-- Section 2: Key inversion lemmas on replicate ++ true :: tail
-- ════════════════════════════════════════════════════════════

/-- countLeadingFalse of (n false-bits followed by true :: tail) equals n. -/
lemma countLeadingFalse_replicate_false_cons_true (n : Nat) (t : BinString) :
    countLeadingFalse (List.replicate n false ++ true :: t) = n := by
  induction n with
  | zero => simp [countLeadingFalse]
  | succ k ih =>
    simp [List.replicate_succ, List.cons_append, countLeadingFalse]
    exact ih

/-- dropPrefix of (n false-bits followed by true :: tail) equals tail. -/
lemma dropPrefix_replicate_false_cons_true (n : Nat) (t : BinString) :
    dropPrefix (List.replicate n false ++ true :: t) = t := by
  induction n with
  | zero => simp [dropPrefix]
  | succ k ih =>
    simp [List.replicate_succ, List.cons_append, dropPrefix]
    exact ih

-- ════════════════════════════════════════════════════════════
-- Section 3: extractFirst and the main inversion lemma
-- ════════════════════════════════════════════════════════════

/-- Extract the first component of a paired BinString.
    On input pair(x, w) = [false^|x|, true] ++ x ++ w,
    this returns x. -/
def extractFirst (s : BinString) : BinString :=
  (dropPrefix s).take (countLeadingFalse s)

/-- The key inversion: extractFirst (pair x w) = x. -/
lemma extractFirst_pair (x w : BinString) : extractFirst (pair x w) = x := by
  unfold extractFirst pair
  -- pair x w = List.replicate x.length false ++ [true] ++ x ++ w
  -- which equals List.replicate x.length false ++ true :: (x ++ w)
  have heq : List.replicate x.length false ++ [true] ++ x ++ w =
             List.replicate x.length false ++ true :: (x ++ w) := by
    simp [List.cons_append, List.append_assoc]
  rw [heq]
  rw [countLeadingFalse_replicate_false_cons_true x.length (x ++ w)]
  rw [dropPrefix_replicate_false_cons_true x.length (x ++ w)]
  -- Now goal: (x ++ w).take x.length = x
  exact List.take_left

-- ════════════════════════════════════════════════════════════
-- Section 4: Construct the projection TM
-- ════════════════════════════════════════════════════════════

/-- Construct M' from M and program p.
    M' ignores its own program p', uses `extractFirst` to decode
    the first component of the paired input, and delegates to M
    with program p. The overhead is 1 step (so c = 1). -/
def mkProjTM (M : StepBoundedTM) (p : BinString) : StepBoundedTM where
  run := fun _p' input steps =>
    if steps = 0 then none
    else M.run p (extractFirst input) (steps - 1)
  run_zero := by
    intro _p' _input
    simp
  run_mono := by
    intro _p' input t₁ t₂ v h_run h_le
    -- h_run : (if t₁ = 0 then none else M.run p (extractFirst input) (t₁ - 1)) = some v
    -- h_le  : t₁ ≤ t₂
    -- split_ifs on h_run: the t₁ = 0 branch gives none = some v (auto-contradiction),
    -- leaving only the t₁ ≠ 0 branch with h_run : M.run p (extractFirst input) (t₁ - 1) = some v
    split_ifs at h_run with ht₁
    -- Only the neg case (¬t₁ = 0) remains; the pos case is closed automatically.
    -- ht₁ : ¬t₁ = 0,  h_run : M.run p (extractFirst input) (t₁ - 1) = some v
    have ht₂ : t₂ ≠ 0 := by omega
    simp [ht₂]
    apply M.run_mono p (extractFirst input) (t₁ - 1) (t₂ - 1) v h_run
    omega

-- ════════════════════════════════════════════════════════════
-- Section 5: Main theorem
-- ════════════════════════════════════════════════════════════

/-- Proved version of tm_pair_proj_exists (eliminates the axiom).

    Given any StepBoundedTM M and program p, we construct:
    - M' = mkProjTM M p  (projects first component and delegates to M)
    - p' = []            (M' ignores its own program)
    - c  = 1             (one extra step for the projection overhead)

    such that M.run p x t = some v → M'.run p' (pair x w) (t + 1) = some v. -/
theorem tm_pair_proj_exists_proved (M : StepBoundedTM) (p : BinString) :
    ∃ (M' : StepBoundedTM) (p' : BinString) (c : Nat),
      ∀ (x w : BinString) (v : BinString) (t : Nat),
        M.run p x t = some v →
        M'.run p' (pair x w) (t + c) = some v := by
  refine ⟨mkProjTM M p, [], 1, ?_⟩
  intro x w v t h_Mrun
  -- M'.run [] (pair x w) (t + 1)
  -- = if (t + 1) = 0 then none else M.run p (extractFirst (pair x w)) (t + 1 - 1)
  simp [mkProjTM]
  -- After simp: M.run p (extractFirst (pair x w)) t = some v
  rw [extractFirst_pair x w]
  exact h_Mrun

-- ════════════════════════════════════════════════════════════
-- Section 6: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms tm_pair_proj_exists_proved

end ClassicalBridge.Complexity.PairProjection
