# TheoremDB P2436 — Least trinomial multiple of a degree-61 binary polynomial

**Author:** Sergey Nefedov  
**Affiliation:** Faculty of Mechanics and Mathematics, Lomonosov Moscow State University  
**Date:** 17 October 2026

This repository provides the computational search and the Lean 4 positive-witness files for TheoremDB [P2436](https://theoremdb.org/statements/P2436/).

## Result

Over `F_2[x]`, with

```text
f(x) = x^61 + x^45 + x^32 + x^2 + 1
```

the least exponent `b` for which `f | x^b + x^a + 1` with `0 < a < b <= 2^31` is

```text
(a,b) = (301682885,848144186)
```

A complete exact collision scan to `B = 2147483648` returns precisely these pairs:

| `a` | `b` | note |
|---:|---:|---|
| 301682885 | 848144186 | minimum `b` |
| 452471585 | 1293170928 | second solution |
| 603365770 | 1696288372 | square of the first trinomial |

The search establishes **computational minimality** by exhausting the complete interval. The included Lean source gives **positive divisibility witnesses**, **not** a Lean proof of minimality. The source originated in a user-supplied `P2436_Lean_checked.zip`; the current packaging machine did not contain Lean, so compilation must be rechecked using the pinned toolchain / GitHub Actions.

## What is in the repository?

| Path | Purpose |
|---|---|
| `paper/P2436_Preprint.pdf` | English scientific preprint |
| `paper/main.tex`, `paper/run_results.tex` | Editable LaTeX source |
| `P2436.lean`, `P2436Poly.lean` | Lean 4 arithmetic theorems and polynomial divisibility bridge |
| `lean-toolchain`, `lakefile.toml` | Lean 4 v4.35.0 / Mathlib v4.35.0 setup |
| `src/exact_search.cpp` | Exact external-bucket search (no hash fingerprints) |
| `verify/verify_witness.py` | Independent carryless-polynomial remainder tests |
| `verify/verify_field.py` | Rabin irreducibility + Lucas–Lehmer + order checks |
| `verify/reference_prefix.py` | Independent dictionary baseline for smaller bounds |
| `results/full_run_summary.json` | Full-run per-partition counts and all witnesses |
| `results/full_search.log` | Output and process resource accounting |
| `tests/test_search.sh` | Compact regression suite |
| `SHA256SUMS` | File integrity checks |

The full search uses about **16 GiB of temporary binary keys**. The large temporary key files are deliberately absent from the distributable ZIP; all code to regenerate them is included.

## Quick checks (no Lean required)

```bash
python3 verify/verify_field.py
python3 verify/verify_witness.py
sh tests/test_search.sh
```

To reproduce the search (native 64-bit Linux or equivalent recommended):

```bash
c++ -O3 -std=c++17 -Wall -Wextra src/exact_search.cpp -o exact_search
./exact_search 2147483648 experiments/full_data
python3 verify/verify_witness.py --summary experiments/full_data/run_summary.json
```

**Disk capacity:** allow more than 16 GiB free (prefer 20+ GiB).  
**RAM:** program loads two arrays of up to the largest partition's size (typically on the order of 128 MiB); the exact peak is workload-dependent.

The algorithm enumerates `alpha^i`, `i=1,...,B` inclusive. It writes the high-bit-discarded keys `alpha^i >> 1` into one of 256 partitions. Five 11-bit radix passes sort all relevant 52 lower key bits exactly in each partition. All duplicate 60-bit keys are extracted and exponent labels reconstructed in another full pass. The full proof of equivalence between duplicate keys and trinomials is given in the article.

### Baseline / historical check

```bash
python3 verify/reference_prefix.py --bound 2000000
```

This returns no pairs and last state `2021773856510245769`, matching the historical TheoremDB baseline.

## Lean 4 verification

With [elan](https://github.com/leanprover/elan) installed:

```bash
lake update
lake exe cache get    # when available, avoids rebuilding Mathlib
lake build
```

All three witnesses are established in Lean bitset arithmetic by `decide +kernel`; `P2436Poly.lean` provides the bridge to divisibility in `(ZMod 2)[X]`. In the supplied certificate archive `P2436_Lean_checked.zip`, these were reported to compile. **Not independently rebuilt in the current packaging runtime.** A GitHub Actions workflow is included to make that status visible when the repository is first pushed.

**Important:** `lake build` does **not** verify the negative exclusion `b < 848144186`. That conclusion requires the full reproducible C++ scan or a future formally verified exhaustive certificate.

## Publication status and scope

The paper is an exact computational result for one specified polynomial. It does not assert the invention of external sorting, collision search, or discrete-logarithm methods. Before journal submission, independently run `lake build` and preferably reproduce the complete scan on a second machine. TheoremDB publicly records only the older exclusion through `2^28` in the examined historical packet; independent priority confirmation is recommended.

Cite as: Sergey Nefedov, *The Least Trinomial Multiple of a Primitive Degree-61 Binary Polynomial: Exact Exhaustive Search and a Lean Verification of the Witnesses*, research preprint (2026).

## License

Software and accompanying material in this repository are distributed under the MIT License (see `LICENSE`). Authors retain responsibility for any later repository identifiers or journal submission metadata.
