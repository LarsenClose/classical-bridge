/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Bridge/SameSemantics.lean -- SameSemantics between
different classical encodings of the same computational domain.

Shows that standard polynomial-time translations between encodings
(e.g., different binary representations of the same problem) satisfy
the SameSemantics interface, and therefore the regime-relevant
properties (UnboundedGap, FiniteDrift) are invariant across them.

CONTENTS:
  1. ReencodingPair: convenience wrapper producing SameSemantics
  2. sameSemantics_refl: every AdmissibleEncoding is SameSemantics with itself
  3. specAdmissibleEncoding: build AdmissibleEncoding from any TMSelfAppSpec
  4. swapPrefixN: bijective prefix-swap on binary strings (same-length headers)
  5. HeaderVariant: two SelfAppHeaders of the same length yield SameSemantics
     encodings, with the prefix-swap as the translation

The key theorem is headerVariant_sameSemantics: if two encodings differ
only in which self-application header they use (and the headers have the
same length), then the encodings satisfy SameSemantics. The translation
is a simple bijection that swaps one header prefix for the other.

STATUS: 0 sorry. Axiom profile: inherits classical_tm_exists and
classical_selfapp_header_exists from UniversalSimulation.lean.
-/

import ClassicalBridge.Mirror.AdmissibleEncoding
import ClassicalBridge.Bridge.TMAdmissibleEncoding

namespace ClassicalBridge.Bridge

open ClassicalBridge ClassicalBridge.TM

-- ════════════════════════════════════════════════════════════
-- Section 1: ReencodingPair — convenience wrapper
-- ════════════════════════════════════════════════════════════

/-- A reencoding pair packages two AdmissibleEncodings of the same
    computational domain together with bounded bijective translations
    that commute with selfApp. This is a thin wrapper that directly
    produces a SameSemantics witness.

    Use case: when you have two encodings and want to show they are
    regime-equivalent, package the translation data into a ReencodingPair
    and extract the SameSemantics via toSameSemantics. -/
structure ReencodingPair where
  /-- The first encoding. -/
  enc₁ : AdmissibleEncoding
  /-- The second encoding. -/
  enc₂ : AdmissibleEncoding
  /-- Forward translation. -/
  translate : enc₁.Names → enc₂.Names
  /-- Backward translation. -/
  translateBack : enc₂.Names → enc₁.Names
  /-- Forward-backward roundtrip. -/
  roundtrip : ∀ x, translateBack (translate x) = x
  /-- Backward-forward roundtrip. -/
  roundtrip' : ∀ y, translate (translateBack y) = y
  /-- The grade overhead of translation. -/
  overhead : Nat
  /-- Forward translation is grade-bounded. -/
  translate_bounded : ∀ x, enc₂.grade (translate x) ≤ enc₁.grade x + overhead
  /-- Backward translation is grade-bounded. -/
  translateBack_bounded : ∀ y, enc₁.grade (translateBack y) ≤ enc₂.grade y + overhead
  /-- Translation commutes with selfApp. -/
  compat : ∀ x,
    enc₂.unfold (enc₂.fold (translate x)) = translate (enc₁.unfold (enc₁.fold x))

/-- Extract a SameSemantics witness from a ReencodingPair. -/
def ReencodingPair.toSameSemantics (rp : ReencodingPair) :
    SameSemantics rp.enc₁ rp.enc₂ where
  translate := rp.translate
  translate_back := rp.translateBack
  translate_roundtrip := rp.roundtrip
  translate_roundtrip' := rp.roundtrip'
  translate_overhead := rp.overhead
  translate_bounded := rp.translate_bounded
  translate_back_bounded := rp.translateBack_bounded
  translate_compat := rp.compat

-- ════════════════════════════════════════════════════════════
-- Section 2: Reflexivity — every encoding is SameSemantics with itself
-- ════════════════════════════════════════════════════════════

/-- Every AdmissibleEncoding is SameSemantics with itself.
    The translation is the identity, overhead is 0. -/
noncomputable def sameSemantics_refl (E : AdmissibleEncoding) : SameSemantics E E where
  translate := id
  translate_back := id
  translate_roundtrip _ := rfl
  translate_roundtrip' _ := rfl
  translate_overhead := 0
  translate_bounded _ := by simp [id]
  translate_back_bounded _ := by simp [id]
  translate_compat _ := rfl

/-- The classicalAdmissibleEncoding is SameSemantics with itself. -/
noncomputable def classical_sameSemantics_refl :
    SameSemantics classicalAdmissibleEncoding classicalAdmissibleEncoding :=
  sameSemantics_refl classicalAdmissibleEncoding

-- ════════════════════════════════════════════════════════════
-- Section 3: specAdmissibleEncoding — generalize classicalAdmissibleEncoding
-- ════════════════════════════════════════════════════════════

/-- Build an AdmissibleEncoding from any TMSelfAppSpec.
    This generalizes classicalAdmissibleEncoding (which uses
    canonicalSpec) to arbitrary self-application specifications.

    Two specAdmissibleEncodings from different specs that share
    the same header length will satisfy SameSemantics (Section 5). -/
noncomputable def specAdmissibleEncoding (spec : TMSelfAppSpec) : AdmissibleEncoding where
  Names := BinString
  fold := tmFold spec.selfAppHeader
  unfold := tmUnfold spec.selfAppHeader
  roundtrip := tmFold_tmUnfold spec.selfAppHeader
  grade := grade
  overhead := spec.selfAppHeader.headerLen
  selfApp_bounded := selfApp_grade_bounded spec.selfAppHeader

/-- specAdmissibleEncoding of canonicalSpec equals classicalAdmissibleEncoding
    in all components. (They are definitionally equal by construction.) -/
theorem specAdmissibleEncoding_canonical_fold (x : BinString) :
    (specAdmissibleEncoding canonicalSpec).fold x =
    classicalAdmissibleEncoding.fold x := rfl

theorem specAdmissibleEncoding_canonical_unfold (x : BinString) :
    (specAdmissibleEncoding canonicalSpec).unfold x =
    classicalAdmissibleEncoding.unfold x := rfl

-- ════════════════════════════════════════════════════════════
-- Section 4: swapPrefixN — bijective prefix swap
-- ════════════════════════════════════════════════════════════

/-- Swap the n-length prefix of a binary string between two headers.
    Given two header strings h₁, h₂ of the same length n:
    - If x starts with h₁, replace the prefix with h₂
    - If x starts with h₂, replace the prefix with h₁
    - Otherwise, leave x unchanged

    When h₁ ≠ h₂ and |h₁| = |h₂| = n, the three cases partition
    all binary strings, and swapPrefixN is a self-inverse bijection:
    swapPrefixN n h₂ h₁ ∘ swapPrefixN n h₁ h₂ = id. -/
def swapPrefixN (n : Nat) (h₁ h₂ : List Bool) (x : List Bool) : List Bool :=
  if x.take n = h₁ then h₂ ++ x.drop n
  else if x.take n = h₂ then h₁ ++ x.drop n
  else x

-- ── Case lemmas ──

private theorem swapPrefixN_case1 (n : Nat) (h₁ h₂ x : List Bool)
    (hpfx : x.take n = h₁) :
    swapPrefixN n h₁ h₂ x = h₂ ++ x.drop n := by
  simp [swapPrefixN, hpfx]

private theorem swapPrefixN_case2 (n : Nat) (h₁ h₂ x : List Bool)
    (_hpfx₁ : ¬(x.take n = h₁)) (hpfx₂ : x.take n = h₂) :
    swapPrefixN n h₁ h₂ x = h₁ ++ x.drop n := by
  unfold swapPrefixN; split <;> simp_all

private theorem swapPrefixN_case3 (n : Nat) (h₁ h₂ x : List Bool)
    (hpfx₁ : ¬(x.take n = h₁)) (hpfx₂ : ¬(x.take n = h₂)) :
    swapPrefixN n h₁ h₂ x = x := by
  unfold swapPrefixN; split <;> simp_all

-- ── List helpers ──

private theorem take_prepend (h rest : List Bool) (n : Nat) (hlen : h.length = n) :
    (h ++ rest).take n = h := by rw [← hlen]; exact List.take_left

private theorem drop_prepend (h rest : List Bool) (n : Nat) (hlen : h.length = n) :
    (h ++ rest).drop n = rest := by rw [← hlen]; exact List.drop_left

-- ── Roundtrip ──

/-- swapPrefixN is an involution (when applied with swapped arguments).
    swapPrefixN n h₂ h₁ ∘ swapPrefixN n h₁ h₂ = id.

    Proof by cases on which prefix x starts with:
    - Starts with h₁: maps to (h₂ ++ tail), which starts with h₂,
      maps back to (h₁ ++ tail) = x.
    - Starts with h₂: maps to (h₁ ++ tail), which starts with h₁,
      maps back to (h₂ ++ tail) = x.
    - Starts with neither: identity in both directions. -/
theorem swapPrefixN_inv (n : Nat) (h₁ h₂ : List Bool)
    (hlen₁ : h₁.length = n) (hlen₂ : h₂.length = n)
    (x : List Bool) :
    swapPrefixN n h₂ h₁ (swapPrefixN n h₁ h₂ x) = x := by
  by_cases hc1 : x.take n = h₁
  · -- Case 1: x starts with h₁ → h₂ ++ tail → starts with h₂ → h₁ ++ tail = x
    rw [swapPrefixN_case1 _ _ _ _ hc1,
        swapPrefixN_case1 _ _ _ _ (take_prepend h₂ (x.drop n) n hlen₂),
        drop_prepend h₂ (x.drop n) n hlen₂, ← hc1]
    exact List.take_append_drop n x
  · by_cases hc2 : x.take n = h₂
    · -- Case 2: x starts with h₂ → h₁ ++ tail → starts with h₁ → h₂ ++ tail = x
      rw [swapPrefixN_case2 _ _ _ _ hc1 hc2]
      have htake := take_prepend h₁ (x.drop n) n hlen₁
      have hneq : h₁ ≠ h₂ := fun heq => hc1 (hc2 ▸ heq ▸ rfl)
      rw [swapPrefixN_case2 _ _ _ _ (by rw [htake]; exact hneq) htake,
          drop_prepend h₁ (x.drop n) n hlen₁, ← hc2]
      exact List.take_append_drop n x
    · -- Case 3: neither prefix → identity both ways
      rw [swapPrefixN_case3 _ _ _ _ hc1 hc2,
          swapPrefixN_case3 _ _ _ _ hc2 hc1]

/-- The reverse direction of the involution. -/
theorem swapPrefixN_inv' (n : Nat) (h₁ h₂ : List Bool)
    (hlen₁ : h₁.length = n) (hlen₂ : h₂.length = n)
    (x : List Bool) :
    swapPrefixN n h₁ h₂ (swapPrefixN n h₂ h₁ x) = x :=
  swapPrefixN_inv n h₂ h₁ hlen₂ hlen₁ x

-- ── Grade bound ──

/-- swapPrefixN adds at most n to the grade (description length).
    In fact: for strings of length >= n the grade is preserved exactly,
    and for short strings the grade is at most n. In both cases,
    grade(result) <= grade(x) + n. -/
theorem swapPrefixN_grade (n : Nat) (h₁ h₂ : List Bool) (x : List Bool)
    (hlen₁ : h₁.length = n) (hlen₂ : h₂.length = n) :
    grade (swapPrefixN n h₁ h₂ x) ≤ grade x + n := by
  unfold swapPrefixN
  split
  · simp [grade, List.length_append, hlen₂, List.length_drop]; omega
  · split
    · simp [grade, List.length_append, hlen₁, List.length_drop]; omega
    · omega

-- ── Drop invariance ──

/-- Dropping n from swapPrefixN gives the same as dropping n from x.
    This is the key lemma for translate_compat: the swap only affects
    the header prefix, leaving the payload (x.drop n) intact. -/
private theorem swap_drop_eq (n : Nat) (h₁ h₂ : List Bool) (x : List Bool)
    (hlen₁ : h₁.length = n) (hlen₂ : h₂.length = n) :
    (swapPrefixN n h₁ h₂ x).drop n = x.drop n := by
  unfold swapPrefixN
  split
  · rw [← hlen₂]; exact List.drop_left
  · split
    · rw [← hlen₁]; exact List.drop_left
    · rfl

/-- Applying swapPrefixN to h₁ ++ tail (a string that starts with h₁)
    always hits Case 1, giving h₂ ++ tail. -/
private theorem swap_on_prefixed (n : Nat) (h₁ h₂ : List Bool) (tail : List Bool)
    (hlen₁ : h₁.length = n) :
    swapPrefixN n h₁ h₂ (h₁ ++ tail) = h₂ ++ tail := by
  have htake : (h₁ ++ tail).take n = h₁ := take_prepend h₁ tail n hlen₁
  simp [swapPrefixN, htake]
  rw [← hlen₁]; exact List.drop_left

-- ════════════════════════════════════════════════════════════
-- Section 5: HeaderVariant — SameSemantics for same-length headers
-- ════════════════════════════════════════════════════════════

/-- Two SelfAppHeaders of the same length define a HeaderVariant.
    The key requirement is that the headers have the same length:
    this is what makes the prefix-swap a bijection.

    CLASSICAL JUSTIFICATION: Different universal TM constructions
    produce self-application headers of different content but often
    of comparable length. Two standard UTMs with equal-length headers
    yield regime-equivalent encodings — their GRMs are connected by
    a BoundedGRMEquiv, so all encoding-invariant properties transfer.

    The same-length restriction is sufficient for the main applications:
    any two headers can be padded to the same length (with corresponding
    adjustments to the UTM), so in practice the restriction is not
    limiting. -/
structure HeaderVariant where
  /-- The first self-application header. -/
  h₁ : SelfAppHeader
  /-- The second self-application header. -/
  h₂ : SelfAppHeader
  /-- The headers have the same length. -/
  sameLen : h₁.headerLen = h₂.headerLen

/-- The first AdmissibleEncoding from a HeaderVariant. -/
noncomputable def HeaderVariant.enc₁ (hv : HeaderVariant) : AdmissibleEncoding :=
  specAdmissibleEncoding ⟨classical_tm_exists, hv.h₁⟩

/-- The second AdmissibleEncoding from a HeaderVariant. -/
noncomputable def HeaderVariant.enc₂ (hv : HeaderVariant) : AdmissibleEncoding :=
  specAdmissibleEncoding ⟨classical_tm_exists, hv.h₂⟩

/-- The forward translation: swap h₁-prefix for h₂-prefix. -/
def HeaderVariant.translate (hv : HeaderVariant) : BinString → BinString :=
  swapPrefixN hv.h₁.headerLen hv.h₁.header hv.h₂.header

/-- The backward translation: swap h₂-prefix for h₁-prefix. -/
def HeaderVariant.translateBack (hv : HeaderVariant) : BinString → BinString :=
  swapPrefixN hv.h₁.headerLen hv.h₂.header hv.h₁.header

-- ── Helper lemmas for the header length equalities ──

private theorem hv_hlen₁ (hv : HeaderVariant) : hv.h₁.header.length = hv.h₁.headerLen :=
  hv.h₁.headerLen_eq.symm

private theorem hv_hlen₂ (hv : HeaderVariant) : hv.h₂.header.length = hv.h₁.headerLen := by
  rw [← hv.h₂.headerLen_eq]; exact hv.sameLen.symm

-- ── The SameSemantics construction ──

/-- MAIN THEOREM: Two header-based encodings with the same header length
    satisfy SameSemantics.

    The translation is the prefix-swap bijection (swapPrefixN). Key properties:

    1. Roundtrip: The swap is an involution — applying it twice recovers
       the original string. This holds because the three cases (starts with
       h₁, starts with h₂, starts with neither) are disjoint when
       |h₁| = |h₂| and h₁ ≠ h₂, and each case maps to a different case
       of the inverse swap.

    2. Grade bound: The swap changes at most the first n characters, so
       the grade changes by at most n = headerLen.

    3. selfApp commutation (translate_compat): Both selfApps strip the
       header prefix and prepend their own header. The swap only changes
       the prefix, so the payload (everything after the first n characters)
       is preserved. Since selfApp operates on the payload via
       unfold(fold(x)) = header ++ x.drop n, and the swap preserves
       x.drop n, both paths through the commutation diagram yield
       h₂.header ++ x.drop n.

    OVERHEAD: headerLen (the common header length). This is the fixed
    constant independent of input size. -/
noncomputable def headerVariant_sameSemantics (hv : HeaderVariant) :
    SameSemantics hv.enc₁ hv.enc₂ where
  translate := hv.translate
  translate_back := hv.translateBack
  translate_roundtrip x := by
    simp only [HeaderVariant.translate, HeaderVariant.translateBack]
    exact swapPrefixN_inv hv.h₁.headerLen hv.h₁.header hv.h₂.header
      (hv_hlen₁ hv) (hv_hlen₂ hv) x
  translate_roundtrip' x := by
    simp only [HeaderVariant.translate, HeaderVariant.translateBack]
    exact swapPrefixN_inv' hv.h₁.headerLen hv.h₁.header hv.h₂.header
      (hv_hlen₁ hv) (hv_hlen₂ hv) x
  translate_overhead := hv.h₁.headerLen
  translate_bounded x := by
    simp only [HeaderVariant.translate, HeaderVariant.enc₁, HeaderVariant.enc₂,
               specAdmissibleEncoding]
    exact swapPrefixN_grade hv.h₁.headerLen hv.h₁.header hv.h₂.header x
      (hv_hlen₁ hv) (hv_hlen₂ hv)
  translate_back_bounded x := by
    simp only [HeaderVariant.translateBack, HeaderVariant.enc₁, HeaderVariant.enc₂,
               specAdmissibleEncoding]
    exact swapPrefixN_grade hv.h₁.headerLen hv.h₂.header hv.h₁.header x
      (hv_hlen₂ hv) (hv_hlen₁ hv)
  translate_compat x := by
    simp only [HeaderVariant.translate, HeaderVariant.enc₁, HeaderVariant.enc₂,
               specAdmissibleEncoding, tmUnfold, tmFold]
    -- LHS: h₂.header ++ (swapPrefixN ... x).drop h₂.headerLen
    -- RHS: swapPrefixN ... (h₁.header ++ x.drop h₁.headerLen)
    -- RHS simplifies via swap_on_prefixed to h₂.header ++ x.drop h₁.headerLen
    rw [swap_on_prefixed hv.h₁.headerLen hv.h₁.header hv.h₂.header
          (x.drop hv.h₁.headerLen) (hv_hlen₁ hv)]
    -- Now both sides are h₂.header ++ ?.drop ?
    congr 1
    rw [← hv.sameLen]
    exact swap_drop_eq hv.h₁.headerLen hv.h₁.header hv.h₂.header x
      (hv_hlen₁ hv) (hv_hlen₂ hv)

/-- Corollary: HeaderVariant induces a BoundedGRMEquiv between the
    GRMs of the two encodings. -/
noncomputable def headerVariant_boundedGRMEquiv (hv : HeaderVariant) :
    BoundedGRMEquiv hv.enc₁.toGRM hv.enc₂.toGRM :=
  (headerVariant_sameSemantics hv).toBoundedGRMEquiv

-- ════════════════════════════════════════════════════════════
-- Section 6: Symmetry of header-based SameSemantics
-- ════════════════════════════════════════════════════════════

/-- SameSemantics is symmetric: if E₁ and E₂ are SameSemantics,
    then so are E₂ and E₁. The translations are simply swapped. -/
noncomputable def sameSemantics_symm {E₁ E₂ : AdmissibleEncoding}
    (S : SameSemantics E₁ E₂) : SameSemantics E₂ E₁ where
  translate := S.translate_back
  translate_back := S.translate
  translate_roundtrip := S.translate_roundtrip'
  translate_roundtrip' := S.translate_roundtrip
  translate_overhead := S.translate_overhead
  translate_bounded := S.translate_back_bounded
  translate_back_bounded := S.translate_bounded
  translate_compat y := by
    -- Need: E₁.unfold (E₁.fold (S.translate_back y)) =
    --       S.translate_back (E₂.unfold (E₂.fold y))
    -- From S.translate_compat for x = S.translate_back y:
    -- E₂.unfold (E₂.fold (S.translate (S.translate_back y))) =
    --   S.translate (E₁.unfold (E₁.fold (S.translate_back y)))
    -- Since S.translate (S.translate_back y) = y:
    -- E₂.unfold (E₂.fold y) = S.translate (E₁.unfold (E₁.fold (S.translate_back y)))
    -- Apply S.translate_back to both sides:
    -- S.translate_back (E₂.unfold (E₂.fold y)) =
    --   S.translate_back (S.translate (E₁.unfold (E₁.fold (S.translate_back y))))
    -- = E₁.unfold (E₁.fold (S.translate_back y))
    have h1 := S.translate_compat (S.translate_back y)
    rw [S.translate_roundtrip'] at h1
    -- h1: E₂.unfold (E₂.fold y) = S.translate (E₁.unfold (E₁.fold (S.translate_back y)))
    -- Apply translate_back to both sides of h1, then use roundtrip
    rw [h1, S.translate_roundtrip]

-- ════════════════════════════════════════════════════════════
-- Axiom audit
-- ════════════════════════════════════════════════════════════

/-
AXIOM INVENTORY for this file:

Custom axioms (inherited from UniversalSimulation.lean, used in
specAdmissibleEncoding and HeaderVariant.enc₁/enc₂):
1. classical_tm_exists : StepBoundedTM
2. classical_selfapp_header_exists : SelfAppHeader

NO NEW AXIOMS are introduced in this file. All theorems about
swapPrefixN (roundtrip, grade bound, drop invariance) and the
SameSemantics constructions (sameSemantics_refl, headerVariant_sameSemantics,
sameSemantics_symm) are PROVED, not axiomatized.

Standard Lean axioms: propext, Quot.sound (from list operations).

NOTE ON THE SAME-LENGTH RESTRICTION:
The HeaderVariant construction requires h₁.headerLen = h₂.headerLen.
This is needed for the prefix-swap to be a bijection. For headers of
different lengths, the swap h₁-prefix ↔ h₂-prefix is not a bijection
on all of BinString (it conflates strings shorter than the longer header).

In practice, the restriction is not limiting: any self-application header
can be padded to a target length by appending no-ops, yielding a new
SelfAppHeader of the desired length with the same computational content.
The same-length case covers the regime-relevant applications.

For the fully general case (arbitrary-length headers), Rogers' isomorphism
theorem guarantees the existence of a computable bijection between any
two acceptable Goedel numberings. Formalizing Rogers' theorem would
require constructing the isomorphism explicitly, which is orthogonal
to the bridge construction.
-/

end ClassicalBridge.Bridge
