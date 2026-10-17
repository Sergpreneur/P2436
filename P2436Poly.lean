import P2436
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# P2436: the bitset computation is arithmetic in `𝔽₂[X]/(f)`

`toPoly s` is the polynomial whose coefficients are the bits `0,…,60` of `s`, and `val s`
its class in `R = 𝔽₂[X]/(f)`.  We prove, for **all** natural-number inputs:

* `val (mulX s) = ξ · val s` (`ξ` the class of `X`);
* `val (mul a b) = val a · val b`;
* `val (xpow n) = ξⁿ` for `n < 2³²`;

hence `isTrinomialMultiple a b = true → f ∣ X^b + X^a + 1` (`divides_of_check`), and the
three kernel-checked witnesses of `P2436.lean` become genuine divisibility statements in
Mathlib's `(ZMod 2)[X]` (`first_divides`, `second_divides`, `squared_divides`).

Author: Nefedov Sergey (Moscow State University, Mathematics Department).
-/

open Polynomial

namespace P2436

/-- `f = X⁶¹ + X⁴⁵ + X³² + X² + 1` over `𝔽₂`. -/
noncomputable def fPoly : (ZMod 2)[X] := X ^ 61 + X ^ 45 + X ^ 32 + X ^ 2 + 1

/-- The polynomial whose coefficients are the bits `0,…,60` of `s`. -/
noncomputable def toPoly (s : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range 61, if s.testBit i then (X : (ZMod 2)[X]) ^ i else 0

/-! ## Characteristic two and bit operations -/

theorem two_eq_zero : (2 : (ZMod 2)[X]) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat Polynomial.C 2, h, map_zero]

theorem add_self (p : (ZMod 2)[X]) : p + p = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

theorem toPoly_xor (a b : ℕ) : toPoly (Nat.xor a b) = toPoly a + toPoly b := by
  show toPoly (a ^^^ b) = _
  unfold toPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> simp [add_self]

theorem toPoly_zero : toPoly 0 = 0 := by simp [toPoly]

theorem toPoly_two_pow {k : ℕ} (hk : k < 61) : toPoly (2 ^ k) = X ^ k := by
  unfold toPoly
  simp only [Nat.testBit_two_pow, decide_eq_true_eq]
  rw [Finset.sum_ite_eq]
  simp [hk]

theorem toPoly_one : toPoly 1 = 1 := by
  simpa using toPoly_two_pow (k := 0) (by norm_num)

theorem toPoly_two : toPoly 2 = X := by
  simpa using toPoly_two_pow (k := 1) (by norm_num)

theorem toPoly_modulusBits : toPoly modulusBits = X ^ 45 + X ^ 32 + X ^ 2 + 1 := by
  rw [show modulusBits = Nat.xor (Nat.xor (Nat.xor (2 ^ 45) (2 ^ 32)) (2 ^ 2)) (2 ^ 0) by decide,
    toPoly_xor, toPoly_xor, toPoly_xor, toPoly_two_pow (by norm_num), toPoly_two_pow (by norm_num),
    toPoly_two_pow (by norm_num), toPoly_two_pow (by norm_num), pow_zero]

/-- Doubling then truncating to 61 bits is multiplication by `X`, up to the `X⁶¹` term. -/
theorem toPoly_double (s : ℕ) :
    toPoly ((2 * s) % 2 ^ 61) + (if s.testBit 60 then X ^ 61 else 0) = X * toPoly s := by
  unfold toPoly
  rw [Finset.sum_range_succ' _ 60, Finset.sum_range_succ _ 60, mul_add, Finset.mul_sum]
  have h0 : ((2 * s) % 2 ^ 61).testBit 0 = false := by
    rw [Nat.testBit_mod_two_pow, Nat.testBit_zero]
    simp
  have hj : ∀ j ∈ Finset.range 60,
      (if ((2 * s) % 2 ^ 61).testBit (j + 1) then (X : (ZMod 2)[X]) ^ (j + 1) else 0) =
        X * (if s.testBit j then X ^ j else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hb : ((2 * s) % 2 ^ 61).testBit (j + 1) = s.testBit j := by
      rw [Nat.testBit_mod_two_pow, ← Nat.testBit_div_two, show 2 * s / 2 = s by omega]
      have : j + 1 < 61 := by omega
      simp [this]
    rw [hb]
    split_ifs <;> simp [pow_succ']
  rw [Finset.sum_congr rfl hj, h0]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  split_ifs <;> ring

/-- **`mulX` is multiplication by `X` modulo `f`** (exactly: up to one multiple of `f`). -/
theorem toPoly_mulX (s : ℕ) :
    toPoly (mulX s) = X * toPoly s + (if s.testBit 60 then fPoly else 0) := by
  have hb : (s / 2 ^ 60 % 2 == 1) = s.testBit 60 := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Bool.beq_eq_decide_eq]
  have hd := toPoly_double s
  unfold mulX
  rw [hb, toPoly_xor, show fieldSize = 2 ^ 61 from rfl]
  cases h60 : s.testBit 60
  · simp only [h60, Bool.false_eq_true, ↓reduceIte, add_zero, toPoly_zero] at hd ⊢
    exact hd
  · simp only [h60, ↓reduceIte] at hd ⊢
    rw [toPoly_modulusBits, ← hd, fPoly]
    linear_combination (-1 : (ZMod 2)[X]) * add_self (X ^ 61 : (ZMod 2)[X])

/-! ## The quotient ring `𝔽₂[X]/(f)` -/

/-- `R = 𝔽₂[X]/(f)`. -/
abbrev R := (ZMod 2)[X] ⧸ Ideal.span ({fPoly} : Set (ZMod 2)[X])

/-- The quotient map. -/
noncomputable def proj : (ZMod 2)[X] →+* R := Ideal.Quotient.mk _

/-- The class of `X`. -/
noncomputable def ξ : R := proj X

/-- The class of the bitset `s`. -/
noncomputable def val (s : ℕ) : R := proj (toPoly s)

theorem proj_f : proj fPoly = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self fPoly)

theorem one_add_one_R : (1 + 1 : R) = 0 := by
  rw [← map_one proj, ← map_add, one_add_one_eq_two, two_eq_zero, map_zero]

theorem val_zero : val 0 = 0 := by rw [val, toPoly_zero, map_zero]

theorem val_one : val 1 = 1 := by rw [val, toPoly_one, map_one]

theorem val_two : val 2 = ξ := by rw [val, toPoly_two, ξ]

theorem val_xor (a b : ℕ) : val (Nat.xor a b) = val a + val b := by
  rw [val, toPoly_xor, map_add, val, val]

theorem val_mulX (s : ℕ) : val (mulX s) = ξ * val s := by
  unfold val ξ
  rw [toPoly_mulX, map_add, map_mul]
  split_ifs <;> simp [proj_f]

/-- `∑_{i<n} bᵢ(b) ξⁱ`. -/
noncomputable def bitsEval (n b : ℕ) : R :=
  ∑ i ∈ Finset.range n, if b.testBit i then ξ ^ i else 0

theorem bitsEval_zero (b : ℕ) : bitsEval 0 b = 0 := by simp [bitsEval]

theorem bitsEval_succ (n b : ℕ) :
    bitsEval (n + 1) b = ξ * bitsEval n (b / 2) + (if b.testBit 0 then 1 else 0) := by
  unfold bitsEval
  rw [Finset.sum_range_succ', Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.testBit_div_two]
    split_ifs <;> simp [pow_succ']

theorem bitsEval_61 (b : ℕ) : bitsEval 61 b = val b := by
  unfold bitsEval val toPoly ξ
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem beq_one_eq_testBit (b : ℕ) : (b % 2 == 1) = b.testBit 0 := by
  rw [Nat.testBit_zero, Bool.beq_eq_decide_eq]

theorem val_mulAux (fuel : ℕ) : ∀ a b acc : ℕ,
    val (mulAux fuel a b acc) = val acc + val a * bitsEval fuel b := by
  induction fuel with
  | zero => intro a b acc; simp [mulAux, bitsEval_zero]
  | succ fuel ih =>
    intro a b acc
    simp only [mulAux]
    rw [ih, val_mulX, bitsEval_succ, beq_one_eq_testBit]
    split_ifs
    · rw [val_xor]; ring
    · ring

/-- **`mul` is multiplication in `𝔽₂[X]/(f)`.** -/
theorem val_mul (a b : ℕ) : val (mul a b) = val a * val b := by
  rw [mul, val_mulAux, bitsEval_61, val_zero, zero_add]

theorem val_powAux (fuel : ℕ) : ∀ base exp acc : ℕ,
    val (powAux fuel base exp acc) = val acc * val base ^ (exp % 2 ^ fuel) := by
  induction fuel with
  | zero => intro base exp acc; simp [powAux, Nat.mod_one]
  | succ fuel ih =>
    intro base exp acc
    simp only [powAux]
    rw [ih, val_mul, Nat.pow_succ', Nat.mod_mul, pow_add, pow_mul]
    split_ifs with hc
    · have h1 : exp % 2 = 1 := by simpa using hc
      rw [h1, val_mul, pow_one]
      ring
    · have h0 : exp % 2 = 0 := by
        have : ¬ exp % 2 = 1 := by simpa using hc
        omega
      rw [h0, pow_zero]
      ring

/-- **`xpow n` is `Xⁿ` modulo `f`** (for `n < 2³²`). -/
theorem val_xpow {n : ℕ} (hn : n < 2 ^ 32) : val (xpow n) = ξ ^ n := by
  rw [xpow, val_powAux, val_one, val_two, one_mul, Nat.mod_eq_of_lt hn]

/-! ## From the Boolean check to divisibility -/

/-- **Soundness of the check.** -/
theorem divides_of_check {a b : ℕ} (h : isTrinomialMultiple a b = true) :
    fPoly ∣ X ^ b + X ^ a + 1 := by
  unfold isTrinomialMultiple at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨_, hab, hb⟩, hx⟩ := h
  have hb' : b < 2 ^ 32 := lt_of_le_of_lt hb (by norm_num)
  have ha' : a < 2 ^ 32 := lt_trans hab hb'
  have hv := congrArg val hx
  rw [val_xor, val_xpow ha', val_xpow hb', val_one] at hv
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change proj (X ^ b + X ^ a + 1) = 0
  rw [map_add, map_add, map_pow, map_pow, map_one]
  change ξ ^ b + ξ ^ a + 1 = 0
  rw [add_comm (ξ ^ b), hv, one_add_one_R]

/-! ## The three witnesses as divisibility in `(ZMod 2)[X]` -/

/-- **First witness:** `f ∣ X^848144186 + X^301682885 + 1` over `𝔽₂`. -/
theorem first_divides :
    (X ^ 61 + X ^ 45 + X ^ 32 + X ^ 2 + 1 : (ZMod 2)[X]) ∣ X ^ 848144186 + X ^ 301682885 + 1 :=
  divides_of_check first_candidate

/-- **Second witness:** `f ∣ X^1293170928 + X^452471585 + 1` over `𝔽₂`. -/
theorem second_divides :
    (X ^ 61 + X ^ 45 + X ^ 32 + X ^ 2 + 1 : (ZMod 2)[X]) ∣ X ^ 1293170928 + X ^ 452471585 + 1 :=
  divides_of_check second_candidate

/-- **Squared witness:** `f ∣ X^1696288372 + X^603365770 + 1` over `𝔽₂`. -/
theorem squared_divides :
    (X ^ 61 + X ^ 45 + X ^ 32 + X ^ 2 + 1 : (ZMod 2)[X]) ∣ X ^ 1696288372 + X ^ 603365770 + 1 :=
  divides_of_check squared_candidate

end P2436
