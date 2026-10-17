/-!
P2436: explicit trinomial multiples of
f = X^61 + X^45 + X^32 + X^2 + 1 over F_2.

Author: Nefedov Sergey (Moscow State University, Mathematics Department).

A bit-vector of coefficients is encoded by a natural number.
This file checks positive witnesses using a completely specified
binary polynomial multiplication/reduction algorithm.

Status (checked with Lean 4.35.0, core library only):
* all three witness theorems are proved by kernel reduction (`decide +kernel`);
  `#print axioms` reports only `propext` — no `native_decide`, no compiler trust;
* `P2436Poly.lean` proves that this computation is exactly arithmetic in
  `𝔽₂[X]/(f)`, so each witness gives `f ∣ X^b + X^a + 1` in Mathlib's `(ZMod 2)[X]`.

This file does NOT formalize minimality of the first witness.

Changes from the submitted draft: `native_decide` → `decide +kernel`;
`modulusBits` and `fieldSize` are no longer `private` (the polynomial
semantics in `P2436Poly.lean` refers to them).
-/

namespace P2436

def modulusBits : Nat := 2^45 + 2^32 + 2^2 + 1
def fieldSize : Nat := 2^61

-- Multiply a residue by X modulo the degree-61 polynomial.
def mulX (s : Nat) : Nat :=
  Nat.xor ((2 * s) % fieldSize)
    (if s / 2^60 % 2 == 1 then modulusBits else 0)

-- Schoolbook multiplication in F_2[X]/(f), 61 coefficient steps.
-- `a` is the current shifted multiplicand, `b` the remaining multiplier.
def mulAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, a, b, acc =>
      mulAux fuel (mulX a) (b / 2)
        (if b % 2 == 1 then Nat.xor acc a else acc)

def mul (a b : Nat) : Nat := mulAux 61 a b 0

-- Binary exponentiation with 32 steps, sufficient for b <= 2^31.
def powAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, base, exp, acc =>
      powAux fuel (mul base base) (exp / 2)
        (if exp % 2 == 1 then mul acc base else acc)

def xpow (n : Nat) : Nat := powAux 32 2 n 1

def isTrinomialMultiple (a b : Nat) : Bool :=
  decide (0 < a ∧ a < b ∧ b ≤ 2^31) &&
    decide (Nat.xor (xpow a) (xpow b) = 1)

-- Kernel-checked computations (no `native_decide`).
theorem first_candidate : isTrinomialMultiple 301682885 848144186 = true := by
  decide +kernel

theorem second_candidate : isTrinomialMultiple 452471585 1293170928 = true := by
  decide +kernel

theorem squared_candidate : isTrinomialMultiple 603365770 1696288372 = true := by
  decide +kernel

end P2436
