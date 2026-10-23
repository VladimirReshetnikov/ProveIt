# Optional compact instance: direct quadratic coding with ten integer unknowns

This standalone optional instance combines the new compact native coefficient
tuple with direct simultaneous quadratic coding. It replaces the quartic source code of the current ten-integer
construction by a direct encoding of all 22 quadratic residuals. A finite B2
(Sidon) sequence gives short digit positions, and one binary carry test checks
all 22 target coefficients simultaneously.

**Result:** a completely specified polynomial in ten unrestricted integer
unknowns, with exact total degree **267,823,432**, evaluated by **786 binary
arithmetic operations**. There are **17 fixed leaves**. ZFC proves that this
polynomial has no integer zero if and only if Con(ZFC).

The improvement is relative to package 31 (`31-sun10`) at ProveIt commit
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`: the previous ten-integer equation has
exact degree 589,042,901,992,797,851,562,527,064 and 1,442 operations. The new degree
is smaller by a factor of about 2.20 × 10^18, with 45.49% fewer operations.
Unknown count stays at ten. No global optimality claim is made.

## Mathematical specification

- `DIRECT_QUADRATIC_PROOF.md`: complete proof of the new source coding step,
  with the coefficient and range bounds needed by the inherited Lucas bridge.
- `generated/direct10_compact.json`: complete division-free circuit; its only variable
  leaves are `f,g,h,k,l,w,x,y,z,m`, all ranging over Z.
- `generated/source_certificate.json`: exact weights, target exponents, residual
  order, coefficient bound, and source hash.
- `data/parent_quartic31.json`: the inherited 31-positive-variable, 22-quadratic
  parent, whose residuals are shifted to the nonnegative domain before coding.
- `data/INSTANCE.json`: exact binding of every fixed leaf. Coefficient recipes
  are embedded in the circuit, in the explicit port order `beta,K0,MC,MF`.
- `coefficients/`: the entire new
  `wang943-checksum67-shared-anchor-length8807-prime581197` native tuple,
  its exact bounded-checksum and rank-control proof, standard-library generator
  and independent audit, literal K215-derived tile data, and all four binary ports.
- `upstream/`: exact inherited mathematical sources and the former circuit for
  comparison. References inside these historical source copies keep their
  original context and are not entry points for this package's build.

The displayed degree is the total degree of the polynomial, not a count of
expanded terms. The binary circuit uses 222 additions, 25 subtractions and 539
multiplications. Constant leaves and reuse are free; multiplication by fixed
numerals and all fixed powers are charged as binary gates.

## Reproduce

Python 3.11+ and its standard library suffice. From any directory:

```sh
python3 /path/to/this/package/reproduce.py
```

The driver reconstructs the four native coefficient payloads, independently
reconstructs their full integers and checks the compact compiler interface, then
rebuilds the literal circuit and checks:

1. all 528 distinct pair sums of the 32-element B2 set (including zero);
2. every simultaneous target coefficient as an exact multivariate polynomial;
3. the native raw-byte hashes and coefficient bit lengths;
4. strict coefficient bounds for the source base 2^1182966;
5. source-circuit transcription modulo three primes;
6. the exact 35-term identity for the final eight-factor norm;
7. a literal DAG comparison with the pinned package-31 downstream finalizer;
8. exact total degree by nonzero diagonal leading coefficients modulo primes;
9. small carry examples and deliberate missing-target/colliding-weight failures.

The authoritative receipt is `verification/RESULTS.json`. These finite checks
are not an end-to-end Lean or Rocq proof. The ordinary proof imports the existing
native compiler/K215 calibration and Sun's mathematical Lucas theorems.
The construction proves an equivalence; it does not prove Con(ZFC).
The optional tuple imports the same native compiler and calibration, adding its
new exact checksum, synchronization and actual-rank adapter proof. Its finite
compiler audit checks 66,062 native identities, 943 exact tile clauses and
38,663 rejected single-bit mutations.

## Compact coefficient metrics

The native base is `B_native=2^590069` (`rho=2^67`, cell length 8807).
The four materialized native ports have bit lengths 590069, 592884, 590069 and
590070 in the order `beta,K0,MC,MF`; they occupy 295,388 raw bytes, or 9,445
bytes as the four provided gzip payloads. These are native-port sizes, not the
height of the expanded ten-variable polynomial.

All four ports are rebound together. The newly recomputed ordinary source
coefficient upper bound has 1,182,954 bits; the source base multiplier is
`beta_source=2^1182966`. The prescribed cap is `2^1065852366 b^1803`.
The unchanged baseline direct construction used source multiplier `2^2134938`.
The compact instance has the same 786 gates and exact degree 267,823,432,
certified independently by diagonal leading residues 88 modulo 101, 70 modulo
1009, and 169595 modulo 1000003.

For the actual-rank completeness construction the prime is `lambda=581197`,
with step `581196`; the controller valuation certificate is
`B_native^581196 mod 581197^2 = 182964883980`.

## Fixed coefficient integrity

The four native ports must be used as one complete tuple. The fourth (`MF`) is
already shifted by the native base minus one. The new source-base constant is
separate from that native base: `beta_source=2^1182966`. Every leaf is specified
by a fixed literal or a finite recipe. There is no unknown recursively enumerable
index and no unbounded coefficient search. Raw binary ports are little-endian.

## Attribution and novelty scope

The B2 finite-field construction is classical (Bose--Chowla). The modified
Lucas bridge is due to Sun; the coprime square merger, quintic merger and final
separating weights are inherited from ProveIt package 31. The new contributions are the compact native bounded-checksum adapter and
the combination with direct simultaneous quadratic coding: no quartic sum of
squares is formed, and exponential base-5 digit positions are replaced by the
explicit short B2 set. The entire downstream finalizer is literally identical
to package 31 after substituting the new source block.

New material was prepared with AI assistance for the ProveIt project. Original
licenses and notices are retained under `licenses/` and `coefficients/licenses/`.
The new code and prose are offered under the MIT-0 terms in `LICENSE`.

Primary references:

- R. C. Bose and S. Chowla, *Theorems in the additive theory of numbers*,
  Comment. Math. Helv. 37 (1962/63), 141–147,
  https://doi.org/10.1007/BF02566968.
- Z.-W. Sun, *Further results on Hilbert's Tenth Problem*, Sci. China Math. 64
  (2021), 281–306, https://arxiv.org/html/1704.03504v7.
- Z.-W. Sun, *Ten unknowns for Hilbert's tenth problem over the integers*,
  preprint (2026), https://arxiv.org/html/2609.01594v2.
