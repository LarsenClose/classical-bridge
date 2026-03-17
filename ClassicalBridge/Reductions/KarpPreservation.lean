/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Reductions/KarpPreservation.lean -- Polynomial-time
Karp reductions and their interaction with the carrier architecture.

A Karp reduction R : A -> B between NP problems, when both are
equipped with AdmissibleEncoding, satisfies SameSemantics if R
commutes with selfApp (translate_compat). Standard parsimonious
reductions satisfy this; arbitrary reductions may not.

The key results:
1. StructurePreservingReduction -> SameSemantics (trivially, by design)
2. ProjectionalPreservation: structure-preserving reductions preserve
   the projectional property (up to bounded drift)
3. Boundary theorem: no structure-preserving reduction exists between
   a projectional encoding and one with UnboundedGap

## Which classical reductions are structure-preserving?

The translate_compat condition (selfApp commutation) is strictly stronger
than answer-preservation. A Karp reduction that merely maps yes-instances
to yes-instances does not need to respect the internal fold/unfold dynamics
of the encoding. Concretely:

- **Parsimonious reductions** (preserve witness count): These naturally
  commute with selfApp because they preserve the combinatorial structure
  that fold/unfold act on. The standard parsimonious reductions between
  NP-complete problems (e.g., SAT -> 3-SAT -> CLIQUE via the Karp/Cook
  chain) are structure-preserving.

- **Arbitrary Karp reductions** (just preserve yes/no): These may
  rearrange the internal structure arbitrarily, breaking the commutation
  with selfApp. A reduction that pads inputs, reorders clauses, or
  introduces dummy variables will generally fail translate_compat.

- **Levin reductions** (preserve witnesses bijectively): These are
  structure-preserving essentially by definition, since the witness
  bijection is exactly the data that makes selfApp commute.

The distinction matters: two problems can be Karp-equivalent (mutually
reducible) without being structure-equivalent (SameSemantics). The regime
classification is only invariant under structure-preserving reductions.

STATUS: 0 sorry.
-/

import ClassicalBridge.Mirror.AdmissibleEncoding

namespace ClassicalBridge.Reductions

-- ════════════════════════════════════════════════════════════
-- Key predicates on AdmissibleEncoding
-- ════════════════════════════════════════════════════════════

/-- An encoding is projectional when selfApp is grade-non-increasing:
    grade(selfApp(x)) <= grade(x) for all x.
    This is the hallmark of PEqNP encodings -- the self-application
    operation does not inflate description complexity. -/
def Projectional (E : AdmissibleEncoding) : Prop :=
  ∀ x, E.grade (E.selfApp x) ≤ E.grade x

/-- An encoding has unbounded gap when the difference between selfApp
    grade and input grade is unbounded: for every bound K, there exists
    some x whose selfApp grade exceeds grade(x) + K.

    This is stronger than merely overflowing fixed thresholds (which is
    compatible with finite drift). UnboundedGap means the grade inflation
    from selfApp grows without limit. -/
def HasUnboundedGap (E : AdmissibleEncoding) : Prop :=
  ∀ K : Nat, ∃ x, E.grade (E.selfApp x) > E.grade x + K

/-- An encoding has finite drift when the selfApp grade increase is
    globally bounded by some constant k: grade(selfApp(x)) <= grade(x) + k
    for all x. This is weaker than Projectional (which requires k = 0)
    but still places the encoding in the bounded-overhead regime.

    Every AdmissibleEncoding has finite drift by definition (with k = overhead),
    but the interest is in the tightest such k. -/
def HasFiniteDrift (E : AdmissibleEncoding) (k : Nat) : Prop :=
  ∀ x, E.grade (E.selfApp x) ≤ E.grade x + k

-- ════════════════════════════════════════════════════════════
-- Basic facts about these predicates
-- ════════════════════════════════════════════════════════════

/-- Projectional implies finite drift with k = 0. -/
theorem projectional_implies_finiteDrift (E : AdmissibleEncoding)
    (hP : Projectional E) : HasFiniteDrift E 0 := by
  intro x
  simp [Nat.add_zero]
  exact hP x

/-- Every AdmissibleEncoding has finite drift with k = overhead. -/
theorem admissible_has_finiteDrift (E : AdmissibleEncoding) :
    HasFiniteDrift E E.overhead := by
  intro x
  exact E.selfApp_bounded x

/-- Projectional and HasUnboundedGap are contradictory on the same encoding.
    If selfApp is grade-non-increasing, the gap is always <= 0,
    so it cannot exceed any K > 0. -/
theorem projectional_not_unboundedGap (E : AdmissibleEncoding)
    (hP : Projectional E) (hU : HasUnboundedGap E) : False := by
  obtain ⟨x, hx⟩ := hU 0
  have h := hP x
  omega

/-- Finite drift with bound k and HasUnboundedGap are contradictory.
    If the gap is bounded by k, it cannot exceed K = k. -/
theorem finiteDrift_not_unboundedGap (E : AdmissibleEncoding) (k : Nat)
    (hF : HasFiniteDrift E k) (hU : HasUnboundedGap E) : False := by
  obtain ⟨x, hx⟩ := hU k
  have h := hF x
  omega

-- ════════════════════════════════════════════════════════════
-- PolyTimeReduction: one-way grade-bounded reduction with section
-- ════════════════════════════════════════════════════════════

/-- A polynomial-time reduction between two admissible encodings.
    This is the one-directional version: reduce embeds E₁ into E₂,
    and lift_back is a section (right inverse for reduce, left inverse
    of the embedding).

    This models a Karp reduction at the encoding level: the function
    reduce maps instances of one problem to instances of another,
    with bounded grade overhead. -/
structure PolyTimeReduction (E₁ E₂ : AdmissibleEncoding) where
  reduce : E₁.Names → E₂.Names
  lift_back : E₂.Names → E₁.Names
  section_roundtrip : ∀ x, lift_back (reduce x) = x
  overhead : Nat
  reduce_bounded : ∀ x, E₂.grade (reduce x) ≤ E₁.grade x + overhead
  lift_back_bounded : ∀ x, E₁.grade (lift_back x) ≤ E₂.grade x + overhead

-- ════════════════════════════════════════════════════════════
-- StructurePreservingReduction: the key strengthening
-- ════════════════════════════════════════════════════════════

/-- A structure-preserving reduction is a full bijection between encodings
    that commutes with selfApp. This is strictly stronger than a
    PolyTimeReduction in two ways:
    1. It requires a full bijection (both roundtrips), not just a section
    2. It requires translate_compat: selfApp commutation

    The commutation condition is what makes this "structure-preserving"
    rather than merely "answer-preserving". It ensures that the reduction
    respects the fold/unfold dynamics, not just the yes/no answers.

    By design, this is exactly SameSemantics. The conversion is trivial. -/
structure StructurePreservingReduction (E₁ E₂ : AdmissibleEncoding) where
  reduce : E₁.Names → E₂.Names
  lift_back : E₂.Names → E₁.Names
  roundtrip : ∀ x, lift_back (reduce x) = x
  roundtrip' : ∀ y, reduce (lift_back y) = y
  overhead : Nat
  reduce_bounded : ∀ x, E₂.grade (reduce x) ≤ E₁.grade x + overhead
  lift_back_bounded : ∀ y, E₁.grade (lift_back y) ≤ E₂.grade y + overhead
  translate_compat : ∀ x,
    E₂.selfApp (reduce x) = reduce (E₁.selfApp x)

-- ════════════════════════════════════════════════════════════
-- StructurePreservingReduction IS SameSemantics
-- ════════════════════════════════════════════════════════════

/-- A StructurePreservingReduction is exactly a SameSemantics witness.
    The conversion is trivial -- they have the same data. -/
def StructurePreservingReduction.toSameSemantics
    {E₁ E₂ : AdmissibleEncoding}
    (R : StructurePreservingReduction E₁ E₂) :
    SameSemantics E₁ E₂ where
  translate := R.reduce
  translate_back := R.lift_back
  translate_roundtrip := R.roundtrip
  translate_roundtrip' := R.roundtrip'
  translate_overhead := R.overhead
  translate_bounded := R.reduce_bounded
  translate_back_bounded := R.lift_back_bounded
  translate_compat := R.translate_compat

/-- Conversely, every SameSemantics witness is a StructurePreservingReduction. -/
def SameSemantics.toStructurePreservingReduction
    {E₁ E₂ : AdmissibleEncoding}
    (S : SameSemantics E₁ E₂) :
    StructurePreservingReduction E₁ E₂ where
  reduce := S.translate
  lift_back := S.translate_back
  roundtrip := S.translate_roundtrip
  roundtrip' := S.translate_roundtrip'
  overhead := S.translate_overhead
  reduce_bounded := S.translate_bounded
  lift_back_bounded := S.translate_back_bounded
  translate_compat := S.translate_compat

/-- Every StructurePreservingReduction induces a BoundedGRMEquiv. -/
def StructurePreservingReduction.toBoundedGRMEquiv
    {E₁ E₂ : AdmissibleEncoding}
    (R : StructurePreservingReduction E₁ E₂) :
    BoundedGRMEquiv E₁.toGRM E₂.toGRM :=
  R.toSameSemantics.toBoundedGRMEquiv

-- ════════════════════════════════════════════════════════════
-- ProjectionalPreservation: structure-preserving reductions
-- transfer bounded grade dynamics
-- ════════════════════════════════════════════════════════════

/-- If E₁ is projectional and R is a structure-preserving reduction
    from E₁ to E₂, then E₂ has finite drift bounded by 2 * R.overhead.

    Proof: For any y in E₂, let x = lift_back(y), so reduce(x) = y.
    grade(E₂.selfApp(y))
      = grade(E₂.selfApp(reduce(x)))       [since y = reduce(x)]
      = grade(reduce(E₁.selfApp(x)))       [by translate_compat]
      ≤ grade(E₁.selfApp(x)) + c           [reduce_bounded]
      ≤ grade(x) + c                        [projectional]
      = grade(lift_back(y)) + c
      ≤ grade(y) + c + c                    [lift_back_bounded]
      = grade(y) + 2c -/
theorem projectionalPreservation
    {E₁ E₂ : AdmissibleEncoding}
    (R : StructurePreservingReduction E₁ E₂)
    (hP : Projectional E₁) :
    HasFiniteDrift E₂ (2 * R.overhead) := by
  intro y
  -- Let x = lift_back(y), so reduce(x) = y
  let x := R.lift_back y
  have hy : R.reduce x = y := R.roundtrip' y
  -- grade(E₂.selfApp(y)) = grade(E₂.selfApp(reduce(x)))
  -- = grade(reduce(E₁.selfApp(x))) by translate_compat
  have h_compat : E₂.selfApp (R.reduce x) = R.reduce (E₁.selfApp x) :=
    R.translate_compat x
  -- Rewrite using y = reduce(x)
  rw [← hy]
  -- Now goal: grade(E₂.selfApp(reduce(x))) ≤ grade(reduce(x)) + 2 * overhead
  rw [h_compat]
  -- Now goal: grade(reduce(E₁.selfApp(x))) ≤ grade(reduce(x)) + 2 * overhead
  have h_red : E₂.grade (R.reduce (E₁.selfApp x)) ≤ E₁.grade (E₁.selfApp x) + R.overhead :=
    R.reduce_bounded (E₁.selfApp x)
  have h_proj : E₁.grade (E₁.selfApp x) ≤ E₁.grade x := hP x
  have h_lift : E₁.grade x ≤ E₂.grade (R.reduce x) + R.overhead := by
    have := R.lift_back_bounded (R.reduce x)
    rw [R.roundtrip] at this
    exact this
  omega

/-- The converse direction: if E₂ is projectional and R is structure-preserving
    E₁ -> E₂, then E₁ has finite drift bounded by 2 * R.overhead.

    This uses the inverse direction: for any x in E₁,
    grade(E₁.selfApp(x))
      = grade(lift_back(reduce(E₁.selfApp(x))))   [by roundtrip]
      = grade(lift_back(E₂.selfApp(reduce(x))))   [by compat]
      ≤ grade(E₂.selfApp(reduce(x))) + c          [lift_back_bounded]
      ≤ grade(reduce(x)) + c                       [projectional on E₂]
      ≤ grade(x) + c + c                           [reduce_bounded] -/
theorem projectionalPreservation_back
    {E₁ E₂ : AdmissibleEncoding}
    (R : StructurePreservingReduction E₁ E₂)
    (hP : Projectional E₂) :
    HasFiniteDrift E₁ (2 * R.overhead) := by
  intro x
  -- grade(E₁.selfApp(x)) = grade(lift_back(reduce(E₁.selfApp(x)))) by roundtrip
  have h_rt : R.lift_back (R.reduce (E₁.selfApp x)) = E₁.selfApp x :=
    R.roundtrip (E₁.selfApp x)
  -- E₂.selfApp(reduce(x)) = reduce(E₁.selfApp(x)) by compat
  have h_compat : E₂.selfApp (R.reduce x) = R.reduce (E₁.selfApp x) :=
    R.translate_compat x
  -- grade(lift_back(reduce(E₁.selfApp(x)))) ≤ grade(reduce(E₁.selfApp(x))) + overhead
  have h1 : E₁.grade (R.lift_back (R.reduce (E₁.selfApp x)))
           ≤ E₂.grade (R.reduce (E₁.selfApp x)) + R.overhead :=
    R.lift_back_bounded (R.reduce (E₁.selfApp x))
  rw [h_rt] at h1
  -- grade(reduce(E₁.selfApp(x))) = grade(E₂.selfApp(reduce(x)))
  rw [← h_compat] at h1
  -- grade(E₂.selfApp(reduce(x))) ≤ grade(reduce(x)) by projectional
  have h2 : E₂.grade (E₂.selfApp (R.reduce x)) ≤ E₂.grade (R.reduce x) := hP (R.reduce x)
  -- grade(reduce(x)) ≤ grade(x) + overhead
  have h3 : E₂.grade (R.reduce x) ≤ E₁.grade x + R.overhead := R.reduce_bounded x
  omega

-- ════════════════════════════════════════════════════════════
-- Boundary theorem: Projectional and UnboundedGap cannot be
-- connected by a StructurePreservingReduction
-- ════════════════════════════════════════════════════════════

/-- If E₁ is projectional and E₂ has unbounded gap, then no
    structure-preserving reduction from E₁ to E₂ can exist.

    Proof: A StructurePreservingReduction would transfer the
    projectional property, giving E₂ finite drift with bound
    2 * overhead. But HasUnboundedGap contradicts any finite drift. -/
theorem boundary_no_structurePreservingReduction
    {E₁ E₂ : AdmissibleEncoding}
    (hP : Projectional E₁)
    (hU : HasUnboundedGap E₂)
    (R : StructurePreservingReduction E₁ E₂) : False := by
  exact finiteDrift_not_unboundedGap E₂ (2 * R.overhead)
    (projectionalPreservation R hP) hU

/-- The symmetric version: if E₁ has unbounded gap and E₂ is projectional,
    no structure-preserving reduction from E₁ to E₂ can exist either.

    Note: StructurePreservingReduction is directional (E₁ -> E₂), but
    the translate_compat condition lets us derive bounds in both directions. -/
theorem boundary_no_structurePreservingReduction_sym
    {E₁ E₂ : AdmissibleEncoding}
    (hU : HasUnboundedGap E₁)
    (hP : Projectional E₂)
    (R : StructurePreservingReduction E₁ E₂) : False := by
  exact finiteDrift_not_unboundedGap E₁ (2 * R.overhead)
    (projectionalPreservation_back R hP) hU

/-- Equivalent formulation: Projectional E₁ and HasUnboundedGap E₂ implies
    any proposed structure-preserving reduction leads to a contradiction. -/
theorem no_structurePreservingReduction_of_boundary
    {E₁ E₂ : AdmissibleEncoding}
    (hP : Projectional E₁)
    (hU : HasUnboundedGap E₂) :
    StructurePreservingReduction E₁ E₂ → False :=
  fun R => boundary_no_structurePreservingReduction hP hU R

-- ════════════════════════════════════════════════════════════
-- Lifting to the GRM level: connection with BoundedGRMEquiv
-- ════════════════════════════════════════════════════════════

/-- The GRM associated to a projectional encoding has PEqNP.
    In fact, selfApp factors through every grade level. -/
theorem projectional_implies_PEqNP (E : AdmissibleEncoding)
    (hP : Projectional E) : PEqNP E.toGRM := by
  exists 0
  intro x hx
  show E.grade (E.unfold (E.fold x)) ≤ 0
  have h := hP x
  unfold Projectional AdmissibleEncoding.selfApp at h
  exact Nat.le_trans h hx

-- Note on the relationship between HasUnboundedGap and SelfAppUnbounded:
--
-- HasUnboundedGap (unbounded gap growth) does NOT imply SelfAppUnbounded
-- (overflows every threshold) in general, because HasUnboundedGap does not
-- constrain WHERE the witnesses live -- they could all be at high grades.
-- SelfAppUnbounded requires witnesses at every grade level.
--
-- Conversely, SelfAppUnbounded does not imply HasUnboundedGap: a constant
-- gap of 1 overflows every threshold but is bounded.
--
-- These are genuinely different conditions. For the boundary theorem,
-- HasUnboundedGap is the right notion because it is what contradicts
-- finite drift (which is what structure-preserving reductions transfer).

-- ════════════════════════════════════════════════════════════
-- Compositional properties
-- ════════════════════════════════════════════════════════════

/-- Structure-preserving reductions compose. If we can reduce E₁ to E₂
    and E₂ to E₃ while preserving structure, we can reduce E₁ to E₃. -/
def StructurePreservingReduction.comp
    {E₁ E₂ E₃ : AdmissibleEncoding}
    (R₁₂ : StructurePreservingReduction E₁ E₂)
    (R₂₃ : StructurePreservingReduction E₂ E₃) :
    StructurePreservingReduction E₁ E₃ where
  reduce x := R₂₃.reduce (R₁₂.reduce x)
  lift_back y := R₁₂.lift_back (R₂₃.lift_back y)
  roundtrip x := by simp [R₂₃.roundtrip, R₁₂.roundtrip]
  roundtrip' y := by simp [R₁₂.roundtrip', R₂₃.roundtrip']
  overhead := R₁₂.overhead + R₂₃.overhead
  reduce_bounded x := by
    have h1 := R₁₂.reduce_bounded x
    have h2 := R₂₃.reduce_bounded (R₁₂.reduce x)
    omega
  lift_back_bounded y := by
    have h1 := R₂₃.lift_back_bounded y
    have h2 := R₁₂.lift_back_bounded (R₂₃.lift_back y)
    omega
  translate_compat x := by
    show E₃.selfApp (R₂₃.reduce (R₁₂.reduce x)) =
         R₂₃.reduce (R₁₂.reduce (E₁.selfApp x))
    rw [R₂₃.translate_compat (R₁₂.reduce x)]
    rw [R₁₂.translate_compat x]

/-- The identity is a structure-preserving reduction (with zero overhead). -/
def StructurePreservingReduction.id (E : AdmissibleEncoding) :
    StructurePreservingReduction E E where
  reduce x := x
  lift_back x := x
  roundtrip _ := rfl
  roundtrip' _ := rfl
  overhead := 0
  reduce_bounded x := by omega
  lift_back_bounded x := by omega
  translate_compat _ := rfl

/-- A structure-preserving reduction can be inverted. -/
def StructurePreservingReduction.symm
    {E₁ E₂ : AdmissibleEncoding}
    (R : StructurePreservingReduction E₁ E₂) :
    StructurePreservingReduction E₂ E₁ where
  reduce := R.lift_back
  lift_back := R.reduce
  roundtrip := R.roundtrip'
  roundtrip' := R.roundtrip
  overhead := R.overhead
  reduce_bounded := R.lift_back_bounded
  lift_back_bounded := R.reduce_bounded
  translate_compat y := by
    -- Need: E₁.selfApp(lift_back(y)) = lift_back(E₂.selfApp(y))
    -- From translate_compat: E₂.selfApp(reduce(x)) = reduce(E₁.selfApp(x))
    -- Let x = lift_back(y), then reduce(x) = y.
    -- E₂.selfApp(y) = E₂.selfApp(reduce(lift_back(y))) = reduce(E₁.selfApp(lift_back(y)))
    -- So lift_back(E₂.selfApp(y)) = lift_back(reduce(E₁.selfApp(lift_back(y))))
    --                               = E₁.selfApp(lift_back(y))
    have h1 : R.reduce (R.lift_back y) = y := R.roundtrip' y
    have h2 : E₂.selfApp (R.reduce (R.lift_back y)) =
              R.reduce (E₁.selfApp (R.lift_back y)) :=
      R.translate_compat (R.lift_back y)
    rw [h1] at h2
    -- h2 : E₂.selfApp y = R.reduce (E₁.selfApp (R.lift_back y))
    -- Goal: E₁.selfApp (R.lift_back y) = R.lift_back (E₂.selfApp y)
    rw [h2, R.roundtrip]

end ClassicalBridge.Reductions
