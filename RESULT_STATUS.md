# What the result proves — and what it does not

- **Proved by independent exact polynomial arithmetic:** all three stated polynomials are divisible by the specified primitive degree-61 binary polynomial.
- **Computational minimality:** obtained by a complete exact key-collision enumeration for all `i=1..2^31`, with all 256 partitions processed and the exponent labels recovered. Code, execution log and 256 counts are distributed.
- **Lean (source supplied by project):** the Lean files encode kernel-oriented Boolean witness checks and a Mathlib quotient-polynomial soundness bridge. No `sorry` / `admit` / custom `axiom` was found in source. The build was not re-executed in the final packaging environment because Lean and Mathlib were not installed.
- **Not yet formalized in Lean:** the global exclusion of all pairs with `b<848144186`.
- **Novelty:** result for a specific instance; no claim of a novel collision-search algorithm or conclusive bibliographic priority review.

For publication, keep these claims distinct.
