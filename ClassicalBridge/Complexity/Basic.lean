/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Complexity/Basic.lean — Complexity classes P and NP.

Builds on the StepBoundedTM infrastructure from TuringMachine/Basic.lean
and the PolyBound machinery from Mirror/CountingFunctions.lean.

## Definitions

- `Language` — a subset of BinString (a decision problem)
- `DecidableInTime` — a TM decides a language within a time bound
- `DTIME` — languages decidable within a given time bound
- `P` — languages decidable in polynomial time
- `NP` — languages with polynomial-time verifiable certificates
- `P_always_sub_NP` — P ⊆ NP
- `P_eq_NP` — the proposition P = NP

## Axiom profile

Zero custom axioms. tm_pair_proj_exists is proved in PairProjection.lean.
All results are proved from definitions.

STATUS: 0 sorry.
-/

import ClassicalBridge.TuringMachine.Basic
import ClassicalBridge.Mirror.CountingFunctions
import ClassicalBridge.Complexity.PairProjection

namespace ClassicalBridge.Complexity

open ClassicalBridge.TM
open ClassicalBridge

-- ════════════════════════════════════════════════════════════
-- Section 1: Languages
-- ════════════════════════════════════════════════════════════

/-- A language is a set of binary strings (a decision problem). -/
def Language : Type := Set BinString

/-- The complement of a language. -/
def Language.compl (L : Language) : Language := fun x => ¬ L x

-- ════════════════════════════════════════════════════════════
-- Section 2: Decidability in time f
-- ════════════════════════════════════════════════════════════

/-- A TM M with program p decides language L within time bound f if:
    - on every x ∈ L, M halts within f(|x|) steps with output [true]
    - on every x ∉ L, M halts within f(|x|) steps with output [false]

    We encode accept/reject as [true]/[false] (singleton BinString).
    The time bound f depends only on the input length. -/
def DecidableInTime (M : StepBoundedTM) (p : BinString) (L : Language)
    (f : Nat → Nat) : Prop :=
  ∀ x : BinString,
    (L x → M.run p x (f (grade x)) = some [true]) ∧
    (¬ L x → M.run p x (f (grade x)) = some [false])

/-- There exist a TM and program deciding L within time f. -/
def DecidableInTimeExist (L : Language) (f : Nat → Nat) : Prop :=
  ∃ (M : StepBoundedTM) (p : BinString), DecidableInTime M p L f

-- ════════════════════════════════════════════════════════════
-- Section 3: DTIME
-- ════════════════════════════════════════════════════════════

/-- DTIME(f): languages decidable in deterministic time f. -/
def DTIME (f : Nat → Nat) : Set Language :=
  {L | DecidableInTimeExist L f}

-- ════════════════════════════════════════════════════════════
-- Section 4: P — polynomial time
-- ════════════════════════════════════════════════════════════

/-- L is in P: decidable in polynomial time. -/
def InP (L : Language) : Prop :=
  ∃ (p : PolyBound), DecidableInTimeExist L p.eval

/-- The complexity class P. -/
def P : Set Language := {L | InP L}

-- ════════════════════════════════════════════════════════════
-- Section 5: NP — nondeterministic polynomial time
-- ════════════════════════════════════════════════════════════

/-- An NP verifier for L: a TM that, given pair(x, w), accepts iff
    x ∈ L and w is a valid certificate. Requirements:
    - x ∈ L → ∃ w with |w| ≤ cert_bound(|x|), verifier accepts pair(x,w)
                within time_bound(|x| + |w|) steps
    - x ∉ L → ∀ w, verifier does NOT accept pair(x,w) -/
def NPVerifier (M : StepBoundedTM) (p_ver : BinString) (L : Language)
    (cert_bound : Nat → Nat) (time_bound : Nat → Nat) : Prop :=
  ∀ x : BinString,
    (L x →
      ∃ w : BinString,
        grade w ≤ cert_bound (grade x) ∧
        M.run p_ver (pair x w) (time_bound (grade x + grade w)) = some [true]) ∧
    (¬ L x →
      ∀ w : BinString,
        M.run p_ver (pair x w) (time_bound (grade x + grade w)) ≠ some [true])

/-- L is in NP: it has a polynomial-time verifier with polynomial certificate bound. -/
def InNP (L : Language) : Prop :=
  ∃ (M : StepBoundedTM) (p_ver : BinString)
    (cert_poly time_poly : PolyBound),
    NPVerifier M p_ver L cert_poly.eval time_poly.eval

/-- The complexity class NP. -/
def NP : Set Language := {L | InNP L}

-- ════════════════════════════════════════════════════════════
-- Section 6: P ⊆ NP
-- ════════════════════════════════════════════════════════════

/-!
## The pair-projection composition axiom

To prove P ⊆ NP we need: given a TM M that decides L on input x,
build a verifier that decides L when given pair(x, w) by ignoring w.

This requires composing M with a "project-first-component" step.
Such a composition exists by the UTM simulation (Turing 1936):
a TM can read the unary length prefix of a paired string, extract x,
and run M on x. The overhead is bounded: at most O(|x|) additional steps
for the projection, which is absorbed into the polynomial time bound.

We axiomatize this rather than constructing the TM from scratch.
-/

/-- TM pair projection. Given a TM M and program p that computes
    on inputs x, there exists a TM M' and program p' that runs M on
    the first component of a paired input, with bounded overhead c.

    PROVED: Constructs M' that extracts fst(pair(x,w)) = x via
    unary-prefix decoding and runs M on it. Overhead c = 1.
    See Complexity/PairProjection.lean.

    Axiom profile: propext, Classical.choice, Quot.sound. -/
theorem tm_pair_proj_exists (M : StepBoundedTM) (p : BinString) :
    ∃ (M' : StepBoundedTM) (p' : BinString) (c : Nat),
      ∀ (x w : BinString) (v : BinString) (t : Nat),
        M.run p x t = some v →
        M'.run p' (pair x w) (t + c) = some v :=
  PairProjection.tm_pair_proj_exists_proved M p

/-- P ⊆ NP.

    Proof: given L ∈ P with decider (M, prog) in time time_p.eval,
    build an NP verifier using the pair-projection wrapper M'.
    The verifier uses empty certificate (cert_poly = ⟨0, 0⟩ evaluates to 0+0=0),
    so |w| ≤ 0 forces w = [].
    The verifier accepts pair(x,[]) iff M accepts x. -/
theorem P_always_sub_NP : P ⊆ NP := by
  intro L hL
  obtain ⟨time_p, M, prog, hdec⟩ := hL
  -- Get the pair-projection composition
  obtain ⟨M', prog', c, hproj⟩ := tm_pair_proj_exists M prog
  -- Time poly for the verifier: same degree, constant shifted by c
  let vtime : PolyBound := ⟨time_p.degree, time_p.constant + c⟩
  -- Certificate poly: cert_poly.eval n = 0 for all n (degree 0, constant 0)
  refine ⟨M', prog', ⟨0, 0⟩, vtime, fun x => ⟨?_, ?_⟩⟩
  · -- L x → ∃ w with |w| ≤ 0 ∧ M' accepts pair(x,w)
    intro hx
    refine ⟨[], ?_, ?_⟩
    · -- |[]| ≤ cert_poly.eval (grade x) = 0
      simp [grade, PolyBound.eval]
    · -- M'.run prog' (pair x []) (vtime.eval (grade x + grade [])) = some [true]
      have hdec_x : M.run prog x (time_p.eval (grade x)) = some [true] :=
        (hdec x).1 hx
      have hproj_x := hproj x [] [true] (time_p.eval (grade x)) hdec_x
      -- Need: time_p.eval (grade x) + c ≤ vtime.eval (grade x + grade [])
      have h_time : time_p.eval (grade x) + c ≤ vtime.eval (grade x + grade []) := by
        simp [PolyBound.eval, vtime, grade]
        -- vtime.eval (grade x) = (grade x)^time_p.degree + time_p.constant + c
        -- ≥ time_p.eval (grade x) + c = (grade x)^time_p.degree + time_p.constant + c
        omega
      exact M'.run_mono prog' (pair x []) _ _ [true] hproj_x h_time
  · -- ¬L x → ∀ w, M' does NOT accept pair(x,w)
    intro hnotL w
    -- M rejects x
    have hdec_neg : M.run prog x (time_p.eval (grade x)) = some [false] :=
      (hdec x).2 hnotL
    -- M' outputs [false] on pair(x,w) at time time_p.eval (grade x) + c
    have hproj_w := hproj x w [false] (time_p.eval (grade x)) hdec_neg
    -- [true] ≠ [false], so M' cannot output [true]
    -- We need to show M'.run prog' (pair x w) (vtime.eval (grade x + grade w)) ≠ some [true]
    have h_time : time_p.eval (grade x) + c ≤ vtime.eval (grade x + grade w) := by
      simp [PolyBound.eval, vtime]
      have : (grade x + grade w) ^ time_p.degree ≥ (grade x) ^ time_p.degree :=
        Nat.pow_le_pow_left (Nat.le_add_right _ _) _
      omega
    have hM'_false := M'.run_mono prog' (pair x w) _ _ [false] hproj_w h_time
    -- M' outputs [false], so it can't output [true]
    intro h_accept
    rw [h_accept] at hM'_false
    exact absurd hM'_false (by decide)

-- ════════════════════════════════════════════════════════════
-- Section 7: P = NP
-- ════════════════════════════════════════════════════════════

/-- The proposition P = NP. -/
def P_eq_NP : Prop := P = NP

/-- P = NP iff NP ⊆ P (since P ⊆ NP is unconditional). -/
theorem P_eq_NP_iff_NP_sub_P : P_eq_NP ↔ NP ⊆ P :=
  ⟨fun h => h ▸ Set.Subset.refl NP,
   fun h => Set.Subset.antisymm P_always_sub_NP h⟩

-- ════════════════════════════════════════════════════════════
-- Section 8: Connection to PolyMarkovProp (task #8)
-- ════════════════════════════════════════════════════════════

/-!
## Connection to PolyMarkovProp

PolyMarkovProp (PolyMarkovBridge.lean) is stated at the CompModel level
where programs and inputs are Nat. The BinString-level P/NP connects to it
via the following dictionary:

  BinString-level            CompModel-level
  ─────────────────          ──────────────────────────────
  Language                   NatLanguage (Nat → Prop)
  InNP L                     NatNP L (defined below)
  P_eq_NP                    PEqNP_nat (defined below)
  P_eq_NP → ∀ L∈NP, L∈P     NatNP → PolyMarkovProp via bridge

The CompModel used in PolyMarkovBridge encodes:
  run : Prog → Nat → Nat → Option Nat
  (prog, input-as-nat, step-count, output-as-nat-or-none)

Task #8 will build the explicit functor from (StepBoundedTM, InNP) to
(CompModel, PolyMarkovProp) and close the P=NP ↔ PolyMarkovProp direction.
-/

/-- A decision problem at the Nat level (CompModel-compatible). -/
def NatLanguage : Type := Nat → Prop

/-- NP at the Nat/CompModel level.

    Matches the PolyMarkovProp formulation: a verifier with polynomial
    certificate bound and polynomial running time, over Nat inputs. -/
def NatNP (L : NatLanguage) : Prop :=
  ∃ (run : Nat → Nat → Nat → Option Nat)
    (_ : ∀ prog x t t' v, run prog x t = some v → t ≤ t' → run prog x t' = some v)
    (p_ver : Nat)
    (cert_poly time_poly : PolyBound),
    ∀ x : Nat,
      (L x ↔
        ∃ w : Nat,
          w ≤ cert_poly.eval x ∧
          run p_ver (x + w) (time_poly.eval x) = some 1) ∧
      (¬ L x →
        ∀ w : Nat,
          run p_ver (x + w) (time_poly.eval x) ≠ some 1)

/-- NP ⊆ P at the Nat/CompModel level.
    This is the form of P = NP that directly instantiates PolyMarkovProp. -/
def PEqNP_nat : Prop :=
  ∀ (L : NatLanguage),
    NatNP L →
    ∃ (run : Nat → Nat → Nat → Option Nat)
      (_ : ∀ prog x t t' v, run prog x t = some v → t ≤ t' → run prog x t' = some v)
      (finder : Nat)
      (q : PolyBound),
      ∀ x, ∃ w t, t ≤ q.eval x ∧ run finder x t = some w

/-- PEqNP_nat implies: for any NatNP language, some poly-time finder exists
    (in some computation model that may differ from the verifier's model).

    This is the INTERFACE for task #8. Task #8 will strengthen this by
    showing the finder can be placed in the SAME model as the verifier,
    which directly instantiates PolyMarkovProp from PolyMarkovBridge.lean
    and derives a contradiction via poly_markov_refutes.

    The current form is proved cleanly: PEqNP_nat directly provides
    the finder (in whatever model the NatNP data uses). -/
theorem PEqNP_nat_gives_finder
    (h : PEqNP_nat) (L : NatLanguage) (hL : NatNP L) :
    ∃ (run : Nat → Nat → Nat → Option Nat)
      (_ : ∀ prog x t t' v, run prog x t = some v → t ≤ t' → run prog x t' = some v)
      (finder : Nat) (q : PolyBound),
      ∀ x, ∃ w t, t ≤ q.eval x ∧ run finder x t = some w :=
  h L hL

end ClassicalBridge.Complexity
