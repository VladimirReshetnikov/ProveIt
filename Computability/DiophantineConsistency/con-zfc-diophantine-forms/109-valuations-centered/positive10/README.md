# Ten positive unknowns: degree 718 in 126 operations

This lane contains the complete fixed polynomial `equation718.json`, its literal
source `circuit718.py`, its ordinary proof `PROOF718.md`, the four exact coefficient
payloads, and finite exact-arithmetic audits. It is calibrated to finite syntactic
ZFC refutability through the inherited package61 source theorem. No new formal
verification inside ZFC, Lean, or Rocq is claimed.

The new polynomial uses the same ten strictly positive unknowns and the same whole
compact44 tuple as the pinned ten-positive degree816 parent. The new count is126
binary operations:74 multiplications,32 additions,20 subtractions. Its exact total
degree is718. This is a degree/operation tradeoff:98 lower degree for2 more additions.

## Main change

Put the factor mu outside the strong Pell square root, instead of inside the
strong Pell ordinate. The smaller ordinate lowers the auxiliary degree while the
scaled root still separates from the other radicals. Center the carrier at both
upper polynomial approximations of the first and strong roots, so the transport
majorant has degree4. Formal Laurent expansions of all16 conjugates prove the
exact718 degree; the finite difference checks independently confirm its attainment.

## Run

From this directory:

```bash
python3 verify718.py
python3 -O verify718.py
```

The audit uses the Python standard library. The complete compact44 coefficient
recipe is in `provenance/compact44/`; its input transition table is included.
The already-materialized fixed integers are in `coefficients/`. `K0` reads
`K.bin.gz`, and `MF` reads `MF_source.bin.gz`: the high mask has already been shifted.
Each gzip file decompresses to its unsigned little-endian coefficient bytes.
All four gzip hashes and decoded hashes are checked before evaluating the circuit.

The source61 report and the ten-positive degree816 parent proof are retained under
`provenance/`; the project snapshot is pinned to
`ec80841c07e91be8956ce6ed4af9a9c0b782d3d9`. Their deeper compiler/calibration chain is
an inherited dependency, with source paths and licenses preserved. The new proof
fully states every changed soundness and completeness argument.

## Domain

The equation is over strictly positive integers. Substitution of x+1 for each
unknown yields a ten-natural-number equation with the same degree and at most10
additional additions. This package does not claim a ten-unrestricted-integer
version.

## Attribution

The parent scaled norm was written for ProveIt by Claude (Anthropic) and credits
several earlier incoming packages. The present radical-only scaling and double
upper-center refinement were developed with OpenAI AI assistance for Vladimir
Reshetnikov. Upstream notices and licenses are retained. No global simplicity
minimum or literature-wide originality assertion is made.
