# Independent review of the compact coefficient instance

The companion script `audit_independent.py` reads only files in this bundle. It
imports neither the native coefficient builder nor the circuit generator. It
was run successfully against circuit SHA256
`b7e4febcbd4ae05ab7af0731675e886646305f785e78bc09b599e8f1d14a51d6`.
The machine-readable receipt is `DIRECT10_COMPACT_INDEPENDENT_AUDIT.json`.

## Exact finite checks

The script reconstructs the native ports directly from the 943 literal tiles,
the 67-bit checksum layout, and the stated padding positions. All four byte
hashes and bit lengths agree with `data/native_coefficients_binding.json`.
The port bit lengths are 590069, 592884, 590069, and 590070 in the order
`beta`, `K0`, `MC`, `MF`.

It independently expands the 22 parent quadratic residuals under the shift
from positive to nonnegative variables. It verifies all 528 unordered pair
sums of the 32 source weights (including zero), all 136 source records, all
22 exact target-coefficient identities, and the source-radix bound with
`beta_source = 2^1182966`. Fifty-four modular fixtures additionally compare
the emitted source circuit to independently evaluated literal source formulas.
These fixtures are regression checks, not universal identity certificates.

The circuit has ten integer variables and 786 live arithmetic operations:
539 multiplications, 222 additions, and 25 subtractions. The syntactic total
degree upper bound is 267823432. Setting every variable equal to one formal
indeterminate, the coefficient at that upper degree is nonzero modulo each
of three primes: 88 modulo 101, 70 modulo 1009, and 169595 modulo 1000003.
Thus the total degree is **exactly 267823432** for this compact coefficient
instance, with no generic-coefficient assumption.

After treating the four source outputs `b`, `X`, `Y`, `Ccap` as boundary
leaves, the finalizer has the same normalized structural hash as the pinned
upstream circuit:
`8c36796cfae5982dcd2eda9b41b49857f1954e6f79f1ed54956dfabf6d1b96c2`.

## Review of the changed native coefficient argument

A separate reading of `coefficients/PROOF.md` found no error in its local
checksum decoder, population accounting, or actual-rank subset argument.
The essential points are recorded here to make the scope concrete.

Every upper checksum contribution is divisible by 1024. There are at most
943 Boolean selectors, so the low mask 1022 first forces the selector count
to be zero or one. With no selector, the received upper word lies in
`[0, 2^41)`, and divisibility by `2^41` forces it to vanish. With one selector,
the upper expression lies strictly between zero and `2^42`, so divisibility
forces precisely `2^41`; the received copy word consequently equals the
selected word. This proves the decoder for every Boolean assignment, before
assuming canonical copy patterns.

The four identifier widths are 8, 9, 8, 9, totaling 34. Four occupation bits
and three anchor bits give the remaining seven bits. Hence each tile word
is `ell + 127*2^34`, with `0 <= ell < 2^34`, and its positive complement
coefficient is `1 + 2^10*(2^34 - ell)`. This is the arithmetic source of the
coefficient-size reduction.

The support population is `943+9+10+9+10+5 = 986`. The new high mask has
122 nonpadding bits and `13*65+19 = 864` padding bits, totaling 986. The low
mask has population `d-986`. The largest product position is 8791, strictly
below the first padding position 8792, and all padding positions are below
8807. These counts and separations agree with the proof's declared layout.

For the rank correction, write `lambda=581197`, `N=lambda^n`, `T=N/lambda`,
and `C0=d*lambda`. The stated order and valuation certificates imply that
the powers of `B^(lambda-1)` enumerate all residues `1+C0*z` modulo `dN`.
The optional separate `B^3` term makes the normalized target nonzero modulo
`lambda`. Its least residue `a` modulo `C0` satisfies
`1 <= a < C0 < T` and `gcd(a,T)=1`. The equation
`a*z0+a*(a-1)/2 = u (mod T)` therefore has a solution. Choosing the orbit
entries with additive coordinates `z0,...,z0+a-1` gives a distinct Boolean
subset even if the coordinates wrap modulo `T`. The maximum cell index,
`N-T-lambda+3`, remains within bounds after either geometrical shift because
`w<T`; the separate cell 3 is distinct and is also safe. The unit certificates
cover every prime divisor of `dN`.

## Scope and dependencies

The compact native tuple is an ordinary mathematical adapter to the named
inherited rotation, language, rectangular-padding, and Pell-interface
results. The independent script establishes finite coefficient bindings,
source arithmetic checks, finalizer identity, operation counts, and exact
degree; it does not provide a proof-assistant formalization of the full
semantic equivalence with ZFC proof search. The explicit parent equations,
source-coding theorem, native compiler argument, and inherited finalizer
lemmas supply that semantic chain. Both the principal instance and this
optional instance state those dependencies explicitly.

Run from any working directory:

```sh
python /absolute/path/to/compact_bundle/verification/audit_independent.py
```
