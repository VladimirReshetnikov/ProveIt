# Author record: a positive actual polynomial zero gives its full word window

Result: author full-source review, fresh module compilation and focused
checks PASS. `controller_certificate` authored this composition at ROOT's
request. It reuses the existing sparse/high-mask word modules and the
frozen fixed-kernel carry endpoint. Independent review of this new
composition is a separate role.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentPolynomialWindow2011.lean | db64a1e9130d09d606f3262781be9a4c0d70db1a9cdb7482cd74ecc0ddf0b730 |
| CurrentPolynomialWindow2011Checks.lean | ff72b23f88db55766e9db1acdd8ccb26cbfc34f009d05ff69d17c84487b54aa7 |
| CurrentSparseDigits2011.lean | 5ce36d1cd28f0162e40d5e7ca712b0e77c7242a1ff9039016fc0765baf50b60d |
| CurrentHighDigits2011.lean | ff6eb32b735f59989d7b21ed835f4c64b5a8bed206a9a4b96a54f25016c35d02 |
| CurrentWindowCarry2011.lean | 94f9ec318d90b66200757bba8992eb6560e283dbdceeac877e48eee80ade3d06 |

`polynomial_zero_window` has exactly two mathematical premises: every
independent coordinate of v is a strictly positive integer, and evaluating
the actual fourteen-variable polynomial at v gives zero. Its four ports
are the entire fixed beta, literal K, low mask, and native high mask plus
beta once. Neither a source solution nor a Boolean word, mask, power
window, temporal phase or native calibration is a premise.

The proof restores one canonical Carrier66 parent and takes its literal
31-coordinate `sourceNat` map. Existing proved source lemmas give all31
coordinate positivities, all22 residual equalities, and the exact original
q, C and integer rank. The original J, F, alpha, z and w are retained at
source coordinates0,1,2,3,10, respectively.

The native source-window theorem then supplies one positive N. Every
subsequent construction uses this same N, avoiding any reconciliation of
independently chosen windows. The low-mask test, positive C and C<q feed
`decode_low_mask`, which constructs the full Boolean word with origin1
and zeros at every unsupported physical position. `high_mask_word` supplies
the actual high mask on that same cyclic type, including the origin digit3
resulting from subtracting one from the repeated cell mask. These prove
all word premises needed by the fixed-port `source_carries` theorem.

The named `Facts` record exposes:

- the positive natural source and every residual equality;
- agreement with the original coordinates, q, C and rank;
- q=`rho^(N*2011)` and J equal to the exact width94517 repunit;
- positive C, its split with F and alpha, and strict F<q-1;
- the full rank population and the actual temporal coefficient
  `w=2^(rank.toNat-47*(N*2011))`;
- the identical temporal rotation, the exact old-z transport equality,
  and the sparse Boolean C word with its origin bit;
- cyclic carries at most57, radix-bounded normalized digits, the quotient
  recurrence and local addition equation;
- normalized word F and every pointwise test against the actual
  `CurrentHighDigits2011.maskDigits`.

The temporal expressions in the carry conclusions use the original
polynomial's rank explicitly. No phase or label-decoding premise is
introduced when changing from the source rank to this rank.

The author fully reread all154+37 final source lines. Both files freshly
compiled serially with `lake env lean -M6000 -j1 -o ...`; the main log is
empty. The checks verify the literal polynomial alias, invoke the endpoint
with only its two stated premises, recover the original positive integer
J/F/w from the natural-coordinate agreements, and verify that the actual
origin mask test uses3. The endpoint's axiom report contains only
`propext`, `Classical.choice`, and `Quot.sound`. Final source hashes were
rechecked unchanged.

| Final log | SHA-256 |
|---|---|
| /tmp/current-polynomial-window2011-final.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| /tmp/current-polynomial-window2011-checks.log | 800a3cab007e99c2dad7d126cf8a70b2323c0378c04e6e1ab95f2b0b10e236fc |

This closes the polynomial-to-arithmetic-word-window composition. It
does not prove one-hot occupation, phase alignment, matched tile labels,
native acceptance, or equivalence with Con(ZFC). Those are subsequent
proof obligations, not assumptions concealed in this endpoint.
