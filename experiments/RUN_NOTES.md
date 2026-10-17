# Full-range fresh replay on 17 October 2026

**Command (fresh run):**

```sh
c++ -O3 -std=c++17 -Wall -Wextra -pedantic src/exact_search.cpp -o .build/exact_search
/usr/bin/time -v .build/exact_search 2147483648 <empty-output-directory>
```

- Exit status: `0`.
- Generation: `2,147,483,648` states, inclusive indices 1 through 2^31.
- Bucket scan: `256/256` complete, literal comparisons of 60-bit keys.
- Duplicate keys: `3`.
- Recovered pairs: `(301682885,848144186)`, `(452471585,1293170928)`, `(603365770,1696288372)`.
- Final state: `263596493844334377`.
- Smallest/largest bucket: `8,379,809` / `8,397,622` records.
- Elapsed: `355.454` seconds (program clock), wall clock `/usr/bin/time` `5:55.49`.
- Peak RSS: `133468` KiB (about `130.34` MiB).
- Original temporary stream: `2^31 * 8` = 16 GiB. Buckets deleted individually after verified scan.
- Audit: `python3 verify/audit_summary.py results/full_run_summary.json` passed.
- Independent exact witness verifier and degree-61 irreducibility/primitivity checks passed.
- Lean was not available on this host: `lake build` not re-executed here; user-supplied checked Lean package is included as source with a CI workflow.

Important: metadata consistency does not by itself prove the program ran faithfully; algorithm review plus full independent re-execution gives stronger assurance. The source and full log are included for that purpose.
