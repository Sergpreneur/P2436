# TheoremDB P2436 — Lean 4 certificate (checked)

Author: Nefedov Sergey (Moscow State University, Mathematics Department).

`f = X^61 + X^45 + X^32 + X^2 + 1` over `F_2`.

## What is proved

| File | Statement | Trust |
| --- | --- | --- |
| `P2436.lean` (core Lean, no Mathlib) | `isTrinomialMultiple a b = true` for (301682885, 848144186), (452471585, 1293170928), (603365770, 1696288372) | kernel only (`decide +kernel`); axioms: `propext` |
| `P2436Poly.lean` (Mathlib v4.35.0) | `f ∣ X^848144186 + X^301682885 + 1`, `f ∣ X^1293170928 + X^452471585 + 1`, `f ∣ X^1696288372 + X^603365770 + 1` in `(ZMod 2)[X]` | standard axioms: `propext`, `Classical.choice`, `Quot.sound` |

`P2436Poly.lean` proves that the bitset algorithm is exactly arithmetic in `F_2[X]/(f)`
(`val_mulX`, `val_mul`, `val_xpow`) and that a passing check implies divisibility
(`divides_of_check`).

**Not proved:** minimality of the first witness (this needs a complete negative search).

## Build

```bash
lean P2436.lean          # core part only, ~5 s
lake build               # both parts (needs Mathlib v4.35.0)
```

Changes from the submitted draft: `native_decide` → `decide +kernel`; `modulusBits`
and `fieldSize` made public; new file `P2436Poly.lean`.
