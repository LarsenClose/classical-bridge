/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Mirror/AdmissibleEncoding.lean — Mirror of AdmissibleEncoding
and SameSemantics from witness-transport/WTS/Tower/CarrierEngineering/AdmissibleBridge.lean.

These are the TARGET INTERFACES that the classical bridge must satisfy.

STATUS: 0 sorry.
-/

import ClassicalBridge.Mirror.GRM

namespace ClassicalBridge

-- ════════════════════════════════════════════════════════════
-- The target interface: AdmissibleEncoding
-- ════════════════════════════════════════════════════════════

/-- An admissible encoding of a computation domain into a graded
    reflexive model. This is the interface that classical polynomial-time
    semantics must satisfy. -/
structure AdmissibleEncoding where
  Names : Type
  fold : Names → Names
  unfold : Names → Names
  roundtrip : ∀ x, fold (unfold x) = x
  grade : Names → Nat
  overhead : Nat
  selfApp_bounded : ∀ x, grade (unfold (fold x)) ≤ grade x + overhead

def AdmissibleEncoding.toGRM (E : AdmissibleEncoding) : GradedReflModel where
  carrier := E.Names
  fold := E.fold
  unfold := E.unfold
  roundtrip := E.roundtrip
  grade := E.grade

def AdmissibleEncoding.selfApp (E : AdmissibleEncoding) (x : E.Names) : E.Names :=
  E.unfold (E.fold x)

-- ════════════════════════════════════════════════════════════
-- The target interface: SameSemantics
-- ════════════════════════════════════════════════════════════

/-- Two admissible encodings represent the same computation semantics
    when bounded translations commute with selfApp. -/
structure SameSemantics (E₁ E₂ : AdmissibleEncoding) where
  translate : E₁.Names → E₂.Names
  translate_back : E₂.Names → E₁.Names
  translate_roundtrip : ∀ x, translate_back (translate x) = x
  translate_roundtrip' : ∀ x, translate (translate_back x) = x
  translate_overhead : Nat
  translate_bounded : ∀ x, E₂.grade (translate x) ≤ E₁.grade x + translate_overhead
  translate_back_bounded : ∀ x, E₁.grade (translate_back x) ≤ E₂.grade x + translate_overhead
  translate_compat : ∀ x,
    E₂.unfold (E₂.fold (translate x)) = translate (E₁.unfold (E₁.fold x))

/-- SameSemantics induces BoundedGRMEquiv. -/
def SameSemantics.toBoundedGRMEquiv {E₁ E₂ : AdmissibleEncoding}
    (S : SameSemantics E₁ E₂) :
    BoundedGRMEquiv E₁.toGRM E₂.toGRM where
  f := S.translate
  g := S.translate_back
  gf := S.translate_roundtrip
  fg := S.translate_roundtrip'
  overhead := S.translate_overhead
  f_bounded := S.translate_bounded
  g_bounded := S.translate_back_bounded
  f_compat := S.translate_compat

end ClassicalBridge
