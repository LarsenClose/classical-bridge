/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Bridge/ChainConnection.lean — Regime classification of the
classical TM model and its relationship to the chain lock theorems.

This file establishes the regime in which classicalGRM (the GRM induced by
classicalAdmissibleEncoding) lives, and documents how this regime relates
to the lock theorems proved in classical-constraints.

KEY RESULTS:
1. classicalGRM has finite drift at overhead = headerLen (inherited from
   the AdmissibleEncoding construction).
2. classicalGRM does NOT have HasUnboundedGap (finite drift contradicts it).
3. classicalGRM does NOT have SelfAppUnbounded (stronger: finite drift
   means selfApp cannot overflow arbitrarily).
4. The chain lock theorems' precondition (SelfAppUnbounded) is not
   satisfied by classicalGRM. Therefore the lock theorems do not
   constrain the classical TM model -- they apply to hypothetical
   models WITH unbounded self-application, and classicalGRM is not one.
5. For classicalGRM to be in the separation regime, the self-application
   header would need to grow without bound as a function of the input.
   But the header is a fixed string (axiom: classical_selfapp_header_exists),
   so this is impossible.

CONNECTION TO classical-constraints:
- classical-constraints proves: TransferHypothesis + SelfAppUnbounded -> False
  (the lock theorems, in BridgeVacuity.lean for each chain).
- classical-bridge proves: classicalGRM has FiniteDrift (this file).
- Therefore: classicalGRM is in the bounded-overhead regime. The lock
  theorems' precondition is not met. The classical TM model does not
  trigger any chain lock.

This is not a deficiency of the lock theorems. The lock theorems correctly
characterize which models WOULD yield separation. The bridge correctly
characterizes which regime the classical model occupies. Together they say:
the classical TM model, with its fixed self-application header, is in the
finite-drift regime, not the separation regime.

STATUS: 0 sorry. Axiom profile: inherits classical_tm_exists and
classical_selfapp_header_exists from UniversalSimulation.lean (via
TMAdmissibleEncoding.lean).
-/

import ClassicalBridge.Bridge.TMAdmissibleEncoding
import ClassicalBridge.Reductions.KarpPreservation

namespace ClassicalBridge.Bridge

open ClassicalBridge.TM
open ClassicalBridge.Reductions

-- ════════════════════════════════════════════════════════════
-- Section 1: classicalGRM regime — finite drift
-- ════════════════════════════════════════════════════════════

/-- The classical GRM has finite drift at its overhead parameter.
    This is the regime-determining fact: the self-application header
    is a fixed-length string, so prepending it and stripping it
    can change the grade by at most headerLen.

    This is immediate from the AdmissibleEncoding construction. -/
theorem classicalGRM_hasFiniteDrift :
    HasFiniteDrift classicalAdmissibleEncoding bridgeOverhead :=
  admissible_has_finiteDrift classicalAdmissibleEncoding

-- ════════════════════════════════════════════════════════════
-- Section 2: classicalGRM does NOT have HasUnboundedGap
-- ════════════════════════════════════════════════════════════

/-- The classical GRM does not have HasUnboundedGap.

    Proof: HasFiniteDrift at any k contradicts HasUnboundedGap.
    classicalGRM has finite drift at k = bridgeOverhead.
    Therefore HasUnboundedGap is impossible.

    This is the first half of the regime classification. -/
theorem classicalGRM_not_hasUnboundedGap :
    ¬ HasUnboundedGap classicalAdmissibleEncoding := by
  intro hU
  exact finiteDrift_not_unboundedGap classicalAdmissibleEncoding
    bridgeOverhead classicalGRM_hasFiniteDrift hU

-- ════════════════════════════════════════════════════════════
-- Section 3: classicalGRM does NOT have SelfAppUnbounded
-- ════════════════════════════════════════════════════════════

/-- Finite drift at bound k implies SelfAppUnbounded is impossible.

    SelfAppUnbounded requires: for every d, there exists x with
    grade(x) <= d and grade(selfApp(x)) > d.

    FiniteDrift at k gives: for all x,
    grade(selfApp(x)) <= grade(x) + k.

    At d = grade(x), this gives grade(selfApp(x)) <= d + k,
    so grade(selfApp(x)) > d only if d + k > d, which means
    the overflow is bounded by k. In particular, at d >= some
    threshold the overflow cannot reach d + k + 1.

    More directly: SelfAppUnbounded at d = 0 gives x with
    grade(x) <= 0 and grade(selfApp(x)) > 0. But finite drift
    gives grade(selfApp(x)) <= grade(x) + k <= 0 + k = k.
    So grade(selfApp(x)) is in {1, ..., k}. This is fine for
    d = 0. But at d = k, SelfAppUnbounded needs x with
    grade(x) <= k and grade(selfApp(x)) > k. Finite drift gives
    grade(selfApp(x)) <= k + k = 2k. So it could still overflow.
    The contradiction comes at d = 2k, 3k, etc. -- but
    SelfAppUnbounded needs overflow at EVERY d.

    Actually, SelfAppUnbounded IS compatible with finite drift:
    a constant gap of 1 overflows every threshold. The right
    negation uses the GRM-level structure.

    The correct statement: finite drift means the GRM induced
    by classicalAdmissibleEncoding cannot have SelfAppUnbounded
    in the STRONGER sense (unbounded gap growth). But
    SelfAppUnbounded (overflow at every threshold) is a different
    condition. See KarpPreservation.lean for the distinction.

    What we CAN prove: the GRM-level SelfAppUnbounded is
    incompatible with finite drift when the drift bound k is
    known. At threshold d, overflow needs grade(selfApp(x)) > d
    with grade(x) <= d. Finite drift gives
    grade(selfApp(x)) <= d + k. So overflow is at most k at
    each level. This is NOT a contradiction with SelfAppUnbounded.

    The real exclusion: SelfAppUnbounded on classicalGRM would
    require, for every d, an x with grade(x) <= d such that
    grade(unfold(fold(x))) > d. But unfold(fold(x)) =
    header ++ x.drop(headerLen), so
    grade(unfold(fold(x))) = headerLen + (grade(x) - min headerLen grade(x)).
    For grade(x) >= headerLen: this equals headerLen + grade(x) - headerLen
    = grade(x). So grade(selfApp(x)) = grade(x) <= d. No overflow.
    For grade(x) < headerLen: this equals headerLen + 0 = headerLen.
    So grade(selfApp(x)) = headerLen. Overflow happens only when
    headerLen > d, i.e., only for d < headerLen.

    Therefore: for d >= headerLen, no overflow is possible.
    SelfAppUnbounded requires overflow at EVERY d.
    Contradiction. -/
theorem classicalGRM_not_selfAppUnbounded :
    ¬ SelfAppUnbounded classicalGRM := by
  intro ⟨overflows⟩
  -- At d = bridgeOverhead, there must be x with grade(x) <= d
  -- and grade(selfApp(x)) > d.
  obtain ⟨x, hxd, hxsa⟩ := overflows bridgeOverhead
  -- But finite drift gives grade(selfApp(x)) <= grade(x) + bridgeOverhead
  have hfd := bridge_selfApp_bounded x
  -- grade(selfApp(x)) = grade(classicalGRM.selfApp x)
  -- = grade(bridgeUnfold(bridgeFold(x)))
  -- which is what bridge_selfApp_bounded bounds.
  -- classicalGRM.selfApp x = bridgeUnfold(bridgeFold(x)) by rfl
  show False
  -- hxd: classicalGRM.grade x <= bridgeOverhead
  -- hxsa: classicalGRM.grade (classicalGRM.selfApp x) > bridgeOverhead
  -- hfd: grade (bridgeUnfold (bridgeFold x)) <= grade x + bridgeOverhead
  -- classicalGRM.grade = grade, classicalGRM.selfApp x = bridgeUnfold (bridgeFold x)
  -- So: grade(bridgeUnfold(bridgeFold(x))) > bridgeOverhead
  -- and: grade(bridgeUnfold(bridgeFold(x))) <= grade(x) + bridgeOverhead
  -- and: grade(x) <= bridgeOverhead
  -- Combining: grade(selfApp(x)) <= bridgeOverhead + bridgeOverhead = 2 * bridgeOverhead
  -- But we need to show > bridgeOverhead is impossible, which it isn't generically.
  -- The issue: finite drift at k allows overflow up to k at each level.
  -- SelfAppUnbounded at d = k is: exists x, grade(x) <= k, grade(selfApp(x)) > k.
  -- Finite drift: grade(selfApp(x)) <= grade(x) + k <= k + k = 2k. So > k is possible.
  -- We need a tighter argument using the specific structure of classicalGRM.
  --
  -- The specific structure: selfApp(x) = header ++ x.drop(headerLen).
  -- grade(selfApp(x)) = headerLen + (grade(x) - min headerLen grade(x))
  -- = headerLen + grade(x) - min headerLen grade(x)
  --
  -- Case 1: grade(x) >= headerLen.
  --   grade(selfApp(x)) = headerLen + grade(x) - headerLen = grade(x) <= d.
  --   No overflow.
  --
  -- Case 2: grade(x) < headerLen.
  --   grade(selfApp(x)) = headerLen + grade(x) - grade(x) = headerLen.
  --   Overflow iff headerLen > d, i.e., d < headerLen.
  --
  -- At d = headerLen = bridgeOverhead:
  --   Case 1: grade(selfApp(x)) = grade(x) <= d. Not > d.
  --   Case 2: grade(selfApp(x)) = headerLen = d. Not > d.
  -- So no x gives overflow at d = bridgeOverhead.
  -- But overflows says there IS such x. Contradiction.
  --
  -- We need to unfold the definitions to get at this.
  -- classicalGRM.grade = classicalAdmissibleEncoding.grade = grade
  -- classicalGRM.selfApp x = classicalGRM.unfold (classicalGRM.fold x)
  --                        = bridgeUnfold (bridgeFold x)
  -- bridgeFold x = tmFold canonicalSpec.selfAppHeader x = x.drop headerLen
  -- bridgeUnfold y = tmUnfold canonicalSpec.selfAppHeader y = header ++ y
  -- So grade(selfApp(x)) = grade(header ++ x.drop headerLen)
  --                       = headerLen + (x.drop headerLen).length
  --                       = headerLen + (grade(x) - headerLen)  ... when grade(x) >= headerLen
  --                       = grade(x)
  --   or = headerLen + 0 = headerLen ... when grade(x) < headerLen
  --
  -- Either way, grade(selfApp(x)) <= max(grade(x), headerLen) = max(grade(x), bridgeOverhead).
  -- Since grade(x) <= bridgeOverhead (from hxd), max(grade(x), bridgeOverhead) = bridgeOverhead.
  -- So grade(selfApp(x)) <= bridgeOverhead. But hxsa says > bridgeOverhead. Contradiction.
  --
  -- The Lean proof needs to compute through these definitions.
  -- grade(selfApp(x)) = (header ++ x.drop headerLen).length
  --                    = header.length + (x.drop headerLen).length
  --                    = headerLen + (x.length - headerLen)
  -- where the subtraction is truncating (Nat).
  -- So grade(selfApp(x)) = headerLen + (grade(x) - headerLen).
  -- Since grade(x) <= bridgeOverhead = headerLen:
  --   grade(x) - headerLen = 0
  --   grade(selfApp(x)) = headerLen = bridgeOverhead
  -- But hxsa: grade(selfApp(x)) > bridgeOverhead. Contradiction with <=.
  --
  -- Let's write the actual proof:
  change classicalGRM.grade (classicalGRM.selfApp x) > bridgeOverhead at hxsa
  have key : classicalGRM.grade (classicalGRM.selfApp x) ≤ bridgeOverhead := by
    -- unfold to get at the list operations
    show grade (bridgeUnfold (bridgeFold x)) ≤ bridgeOverhead
    simp only [bridgeUnfold, bridgeFold, canonicalSpec, TMSelfAppSpec.unfold,
               TMSelfAppSpec.fold, tmUnfold, tmFold, grade, List.length_append,
               List.length_drop]
    -- Now goal: headerLen + (x.length - headerLen) <= bridgeOverhead
    -- where bridgeOverhead = headerLen
    show classical_selfapp_header_exists.header.length +
         (x.length - classical_selfapp_header_exists.headerLen) ≤
         classical_selfapp_header_exists.headerLen
    rw [classical_selfapp_header_exists.headerLen_eq]
    -- Now: header.length + (x.length - header.length) <= header.length
    -- Since grade(x) <= bridgeOverhead = headerLen = header.length (from hxd):
    have hxlen : x.length ≤ classical_selfapp_header_exists.header.length := by
      have := hxd
      simp only [classicalGRM, classicalAdmissibleEncoding, AdmissibleEncoding.toGRM,
                 grade, bridgeOverhead, canonicalSpec, TMSelfAppSpec.overhead] at this
      rw [classical_selfapp_header_exists.headerLen_eq] at this
      exact this
    omega
  omega

-- ════════════════════════════════════════════════════════════
-- Section 4: Why the self-application header MUST be fixed
-- ════════════════════════════════════════════════════════════

-- For classicalGRM to have SelfAppUnbounded, the self-application
-- overhead would need to grow without bound. Specifically, at each
-- threshold d, there would need to be an input x with grade(x) <= d
-- whose selfApp grade exceeds d.
--
-- In the classical TM model, selfApp(x) = header ++ x.drop(headerLen).
-- The grade of selfApp(x) is headerLen + (grade(x) - headerLen) when
-- grade(x) >= headerLen, or headerLen when grade(x) < headerLen.
--
-- For grade(x) >= headerLen: grade(selfApp(x)) = grade(x). No overflow.
-- For grade(x) < headerLen: grade(selfApp(x)) = headerLen.
-- Overflow above threshold d requires headerLen > d.
--
-- So overflow is possible only at thresholds d < headerLen. Since
-- headerLen is a fixed constant, SelfAppUnbounded (overflow at ALL
-- thresholds) is impossible.
--
-- To get SelfAppUnbounded, one would need a model where the "header"
-- grows with the input — but then it would not be a fixed self-application
-- header. Such a model does not correspond to standard Turing machine
-- computation, where the universal simulation overhead is fixed.

-- ════════════════════════════════════════════════════════════
-- Section 5: The classical model satisfies PEqNP-like conditions
-- ════════════════════════════════════════════════════════════

/-- selfApp on classicalGRM factors through every grade level
    at or above bridgeOverhead.

    For any d >= bridgeOverhead and any x with grade(x) <= d:
    grade(selfApp(x)) <= max(grade(x), bridgeOverhead) <= d.

    This means classicalGRM satisfies FactorsThrough at level
    d = bridgeOverhead, which is PEqNP (there exists a grade
    through which selfApp factors). -/
theorem classicalGRM_factorsThrough :
    FactorsThrough classicalGRM classicalGRM.selfApp bridgeOverhead := by
  intro x hx
  -- grade(selfApp(x)) <= grade(x) + bridgeOverhead by finite drift
  -- But we can do better: grade(selfApp(x)) <= max(grade(x), bridgeOverhead)
  -- Since grade(x) <= bridgeOverhead, this gives <= bridgeOverhead.
  show classicalGRM.grade (classicalGRM.selfApp x) ≤ bridgeOverhead
  -- Unfold to list operations
  show grade (bridgeUnfold (bridgeFold x)) ≤ bridgeOverhead
  simp only [bridgeUnfold, bridgeFold, canonicalSpec, TMSelfAppSpec.unfold,
             TMSelfAppSpec.fold, tmUnfold, tmFold, grade, List.length_append,
             List.length_drop]
  show classical_selfapp_header_exists.header.length +
       (x.length - classical_selfapp_header_exists.headerLen) ≤
       classical_selfapp_header_exists.headerLen
  rw [classical_selfapp_header_exists.headerLen_eq]
  have hxlen : x.length ≤ classical_selfapp_header_exists.header.length := by
    have := hx
    simp only [classicalGRM, classicalAdmissibleEncoding, AdmissibleEncoding.toGRM,
               grade, bridgeOverhead, canonicalSpec, TMSelfAppSpec.overhead] at this
    rw [classical_selfapp_header_exists.headerLen_eq] at this
    exact this
  omega

/-- classicalGRM satisfies PEqNP: selfApp factors through some grade. -/
theorem classicalGRM_PEqNP : PEqNP classicalGRM :=
  ⟨bridgeOverhead, classicalGRM_factorsThrough⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: classicalAdmissibleEncoding is projectional
-- at or above the overhead threshold
-- ════════════════════════════════════════════════════════════

/-- For inputs at or above the overhead threshold, selfApp does not
    increase the grade at all. This is the structural content of the
    fixed header: for "long enough" inputs, stripping and re-prepending
    the header is lossless.

    Specifically, when grade(x) >= headerLen:
    grade(selfApp(x)) = headerLen + (grade(x) - headerLen) = grade(x). -/
theorem classicalGRM_selfApp_grade_large (x : BinString)
    (hx : grade x ≥ bridgeOverhead) :
    classicalGRM.grade (classicalGRM.selfApp x) = classicalGRM.grade x := by
  show grade (bridgeUnfold (bridgeFold x)) = grade x
  simp only [bridgeUnfold, bridgeFold, canonicalSpec, TMSelfAppSpec.unfold,
             TMSelfAppSpec.fold, tmUnfold, tmFold, grade, List.length_append,
             List.length_drop]
  show classical_selfapp_header_exists.header.length +
       (x.length - classical_selfapp_header_exists.headerLen) = x.length
  rw [classical_selfapp_header_exists.headerLen_eq]
  have hxlen : x.length ≥ classical_selfapp_header_exists.header.length := by
    have := hx
    simp only [bridgeOverhead, canonicalSpec, TMSelfAppSpec.overhead, grade] at this
    rw [classical_selfapp_header_exists.headerLen_eq] at this
    exact this
  omega

/-- For inputs below the overhead threshold, selfApp returns a string of
    exactly headerLen. This is because fold strips more characters than
    exist, yielding [], and unfold prepends the full header. -/
theorem classicalGRM_selfApp_grade_small (x : BinString)
    (hx : grade x < bridgeOverhead) :
    classicalGRM.grade (classicalGRM.selfApp x) ≤ bridgeOverhead := by
  show grade (bridgeUnfold (bridgeFold x)) ≤ bridgeOverhead
  simp only [bridgeUnfold, bridgeFold, canonicalSpec, TMSelfAppSpec.unfold,
             TMSelfAppSpec.fold, tmUnfold, tmFold, grade, List.length_append,
             List.length_drop]
  show classical_selfapp_header_exists.header.length +
       (x.length - classical_selfapp_header_exists.headerLen) ≤
       classical_selfapp_header_exists.headerLen
  rw [classical_selfapp_header_exists.headerLen_eq]
  have hxlen : x.length < classical_selfapp_header_exists.header.length := by
    have := hx
    simp only [bridgeOverhead, canonicalSpec, TMSelfAppSpec.overhead, grade] at this
    rw [classical_selfapp_header_exists.headerLen_eq] at this
    exact this
  omega

-- ════════════════════════════════════════════════════════════
-- Section 7: Connection to the chain lock theorems
-- ════════════════════════════════════════════════════════════

/-!
## Connection to the chain lock theorems in classical-constraints

The chain lock theorems (in classical-constraints) prove results of the form:

  TransferHypothesis + SelfAppUnbounded -> False

for various chains (SAT, proof complexity, descriptive complexity, CSP,
algebraic proof systems, extension complexity, protocol).

The bridge (this repo) proves:

  classicalGRM has finite drift at overhead = headerLen
  classicalGRM does NOT have SelfAppUnbounded
  classicalGRM satisfies PEqNP

These results connect as follows:

### What the lock theorems say

The lock theorems characterize which models are in the separation regime.
A model M is in the separation regime when SelfAppUnbounded holds for M.
The lock theorems prove that in such models, certain bridge conditions
(TransferHypothesis) are uninhabitable. This means: if a model has
unbounded self-application, then no faithful translation can exist between
the SAT/algebraic/descriptive/... type system and the graded model's
type system.

### What the bridge says

The bridge characterizes which regime the classical TM model occupies.
classicalGRM has a fixed self-application header of length headerLen.
This makes selfApp = "prepend header, strip header" -- an operation
with bounded (in fact, asymptotically zero) grade inflation.

Specifically:
- For grade(x) >= headerLen: grade(selfApp(x)) = grade(x). Zero drift.
- For grade(x) < headerLen: grade(selfApp(x)) = headerLen. Bounded.

So classicalGRM is firmly in the finite-drift / PEqNP regime.

### How they connect

The lock theorems' precondition (SelfAppUnbounded) is NOT satisfied by
classicalGRM. Therefore:

1. The lock theorems do not constrain classicalGRM. They apply to a
   different class of models -- those where self-application has
   unbounded grade growth.

2. A TransferHypothesis for classicalGRM is NOT a priori blocked by
   the lock theorems. Whether such a transfer exists is an independent
   question about the relationship between SAT instances and the
   classical GRM.

3. The regime classification is: classicalGRM is in the PEqNP regime.
   This does not mean P = NP in the complexity-theoretic sense. It means
   the self-application operation on binary strings, as formalized by
   the fixed-header fold/unfold pair, has bounded grade overhead.

### What WOULD be needed for separation

For classicalGRM to be in the separation regime (SelfAppUnbounded),
the self-application operation would need to produce unbounded grade
growth. This would require:

- The self-application "header" to grow with the input size, OR
- The fold operation to amplify information rather than discard it, OR
- A fundamentally different model where self-interpretation costs
  grow without bound as a function of program size.

None of these hold for standard Turing machine computation. The UTM
has a fixed finite description, the self-application header is a
fixed string derived from the Kleene recursion theorem, and fold
(drop headerLen) discards a fixed prefix.

### The structural picture

The lock theorems and the bridge together give a complete picture:

  Lock theorems: SelfAppUnbounded models cannot have faithful transfers.
  Bridge: classicalGRM is NOT a SelfAppUnbounded model.
  Together: the lock theorems' impossibility results do not apply to
  the classical TM model. The classical model lives in a different
  regime -- the one where self-application has bounded overhead.

This is not a gap in the argument. It is the structural resolution:
the P vs NP question, when formalized through the carrier architecture,
is a question about which regime the computation model occupies. The
classical TM model occupies the finite-drift regime. The lock theorems
characterize the separation regime. These are different regimes, and
the boundary between them is proved invariant (in witness-transport).
-/

-- ════════════════════════════════════════════════════════════
-- Section 8: Summary theorem
-- ════════════════════════════════════════════════════════════

/-- Complete regime classification for classicalGRM.

    The classical TM model, with its fixed self-application header:
    (1) Has finite drift at overhead = bridgeOverhead
    (2) Does not have HasUnboundedGap
    (3) Does not have SelfAppUnbounded
    (4) Satisfies PEqNP (selfApp factors through grade bridgeOverhead)
    (5) Is asymptotically projectional (zero drift for inputs above
        the overhead threshold) -/
theorem classicalGRM_regime_classification :
    -- (1) Finite drift
    HasFiniteDrift classicalAdmissibleEncoding bridgeOverhead ∧
    -- (2) No unbounded gap
    ¬ HasUnboundedGap classicalAdmissibleEncoding ∧
    -- (3) No SelfAppUnbounded
    ¬ SelfAppUnbounded classicalGRM ∧
    -- (4) PEqNP
    PEqNP classicalGRM :=
  ⟨classicalGRM_hasFiniteDrift,
   classicalGRM_not_hasUnboundedGap,
   classicalGRM_not_selfAppUnbounded,
   classicalGRM_PEqNP⟩

-- ════════════════════════════════════════════════════════════
-- Axiom audit
-- ════════════════════════════════════════════════════════════

/-
AXIOM INVENTORY for ChainConnection.lean:

Custom axioms (inherited from UniversalSimulation.lean via TMAdmissibleEncoding.lean):
1. classical_tm_exists : StepBoundedTM
2. classical_selfapp_header_exists : SelfAppHeader

Standard Lean axioms: propext, Quot.sound (from list operations).

All theorems in this file are PROVED, not axiomatized.
The proofs use:
- The AdmissibleEncoding interface (roundtrip, selfApp_bounded)
- Direct unfolding to list operations (List.length_append, List.length_drop)
- The SelfAppHeader.headerLen_eq field (headerLen = header.length)
- Basic arithmetic (omega)

No additional axioms beyond those already used by TMAdmissibleEncoding.
-/

end ClassicalBridge.Bridge
