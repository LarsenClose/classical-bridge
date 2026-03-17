/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalBridge/Encoding/BinaryEncoding.lean — Binary string encodings
for standard computational objects.

Provides encodings of: natural numbers, pairs, and lists as binary strings,
with explicit grade (length) bounds.

The carrier type is `List Bool` (BinString), grade = List.length.

STATUS: 0 sorry.
-/

import ClassicalBridge.TuringMachine.Basic
import Mathlib.Data.Nat.Log

namespace ClassicalBridge.Encoding

open ClassicalBridge.TM

-- ════════════════════════════════════════════════════════════
-- Section 1: Nat encoding (binary, LSB first)
-- ════════════════════════════════════════════════════════════

/-- Encode a natural number as a binary string (LSB first).
    0 maps to [], positive n maps to the binary digits of n.
    This is the standard positional encoding read right to left. -/
def encodeNat : Nat → BinString
  | 0 => []
  | n + 1 =>
    let bit : Bool := (n + 1) % 2 == 1
    bit :: encodeNat ((n + 1) / 2)
  termination_by n => n
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (by omega) (by omega)

/-- Decode a binary string (LSB first) back to a natural number. -/
def decodeNat : BinString → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * decodeNat bs

/-- Length of encodeNat output. -/
theorem length_encodeNat_succ (n : Nat) (h : n > 0) :
    (encodeNat n).length = (encodeNat (n / 2)).length + 1 := by
  match n, h with
  | n + 1, _ =>
    simp [encodeNat]

theorem decodeNat_encodeNat : ∀ (n : Nat), decodeNat (encodeNat n) = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => simp [encodeNat, decodeNat]
    | n + 1 =>
      simp only [encodeNat, decodeNat]
      have hdiv : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by omega)
      rw [ih _ hdiv]
      simp only [beq_iff_eq]
      split <;> omega

/-- Grade bound for Nat encoding. We prove the simple linear bound
    grade(encodeNat n) ≤ n, which is sufficient for the bridge.
    (The tight bound is ⌊log₂ n⌋ + 1 for n > 0.) -/
theorem grade_encodeNat_le : ∀ (n : Nat), grade (encodeNat n) ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => simp [encodeNat, grade]
    | n + 1 =>
      simp only [encodeNat, grade, List.length_cons]
      have hdiv : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by omega)
      have h1 := ih _ hdiv
      simp only [grade] at h1
      have h2 : (n + 1) / 2 ≤ n := by omega
      omega

-- ════════════════════════════════════════════════════════════
-- Section 2: Pair encoding (length-prefixed)
-- ════════════════════════════════════════════════════════════

/-- Encode a length as a unary prefix: n is encoded as n copies of `true`
    followed by one `false` sentinel. This gives a self-delimiting prefix. -/
def encodeLength (n : Nat) : BinString :=
  List.replicate n true ++ [false]

theorem grade_encodeLength (n : Nat) :
    grade (encodeLength n) = n + 1 := by
  simp [encodeLength, grade, List.length_append, List.length_replicate]

/-- Decode a unary-encoded length prefix. Returns (length, remaining string). -/
def decodeLength : BinString → Nat × BinString
  | [] => (0, [])
  | false :: rest => (0, rest)
  | true :: rest =>
    let (n, remaining) := decodeLength rest
    (n + 1, remaining)

theorem decodeLength_replicate_true_cons_false (n : Nat) (rest : BinString) :
    decodeLength (List.replicate n true ++ (false :: rest)) = (n, rest) := by
  induction n with
  | zero => simp [decodeLength]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, decodeLength]
    rw [show (decodeLength (List.replicate n true ++ false :: rest)) =
      (n, rest) from ih]

theorem decodeLength_encodeLength (n : Nat) (rest : BinString) :
    decodeLength (encodeLength n ++ rest) = (n, rest) := by
  simp only [encodeLength, List.append_assoc, List.singleton_append]
  exact decodeLength_replicate_true_cons_false n rest

/-- Encode a pair of binary strings. Format: |a| in unary, then a, then b. -/
def encodePair (a b : BinString) : BinString :=
  encodeLength a.length ++ a ++ b

/-- Decode a pair of binary strings. -/
def decodePair (s : BinString) : BinString × BinString :=
  let (lenA, rest) := decodeLength s
  (rest.take lenA, rest.drop lenA)

theorem decodePair_encodePair (a b : BinString) :
    decodePair (encodePair a b) = (a, b) := by
  simp only [decodePair, encodePair, List.append_assoc]
  rw [decodeLength_encodeLength]
  simp

/-- Grade of encoded pair. -/
theorem grade_encodePair (a b : BinString) :
    grade (encodePair a b) = 2 * grade a + grade b + 1 := by
  simp [encodePair, grade, List.length_append, encodeLength, List.length_replicate]
  omega

/-- The pair encoding overhead is linear in grade(a):
    grade(encodePair a b) ≤ 2 * grade(a) + grade(b) + 1. -/
theorem grade_encodePair_le (a b : BinString) :
    grade (encodePair a b) ≤ 2 * grade a + grade b + 1 := by
  rw [grade_encodePair]

-- ════════════════════════════════════════════════════════════
-- Section 3: List encoding
-- ════════════════════════════════════════════════════════════

/-- Encode a list of binary strings. Each element is length-prefixed
    using the unary encoding, making the format self-delimiting. -/
def encodeList : List BinString → BinString
  | [] => []
  | x :: xs => encodeLength x.length ++ x ++ encodeList xs

/-- Grade bound for list encoding: total length is bounded by
    twice the sum of element lengths plus the number of elements. -/
theorem grade_encodeList_le (xs : List BinString) :
    grade (encodeList xs) ≤ 2 * (xs.map grade).sum + xs.length := by
  induction xs with
  | nil => simp [encodeList, grade]
  | cons x xs ih =>
    simp only [encodeList, grade, List.length_append]
    simp only [encodeLength, List.length_append, List.length_replicate,
      List.length_singleton]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    simp only [grade] at ih ⊢
    omega

end ClassicalBridge.Encoding
