# Independent finite certificate for the complemented three-anchor radix47 tuple

The finite condition **Pc3 passes**, with
`lambda = 1012691 = 10*101269 + 1 > d = 47*8807 = 413929`.
This discharges the numerical controller condition in section 11 of
[`../compact66-complemented-three-anchor-radix47/README.md`](../compact66-complemented-three-anchor-radix47/README.md).
It does not certify the complete native or Pell arguments, or promote the
maintained equation. Those are separate mathematical and review obligations.

The newly authored 297-line [`certify.py`](certify.py) uses only the Python standard
library and was read completely before its first execution; changed portions
were inspected before subsequent runs. No incoming script, project module,
saved coefficient array or earlier numerical controller output is executed or
imported. Its formula transcription was made from the complete maintained
[`../../equation.tex`](../../equation.tex) and the complete source proof above.
The equation input is pinned to the unchanged
[`../../candidates/one-page-compact66-radix55/equation.tex`](../../candidates/one-page-compact66-radix55/equation.tex)
copy, whose bytes match the maintained page used for transcription.
The proof is read only for its exact hash by the program: mathematical
transcription of its formulas is explicit in the small verifier.

Run from the repository root, using Python 3.10 or newer:

```sh
python3 Computability/DiophantineConsistency/research/complemented47-controller-independent/certify.py
```

The default command is read-only and requires exact byte agreement with
[`certificate.json`](certificate.json). Every gate uses an explicit exception,
so Python's `-O` option does not disable verification. Normal and `-O` reruns
both reproduced the saved evidence exactly. To intentionally regenerate the
receipt after reviewing a change, append `--write`; that mode writes only
`certificate.json`.
It extracts the full 436-character seed from the maintained page, reconstructs
all 430 actions and all 943 uniquely indexed tiles, and forms all 3297
coefficients, including every zero. Tile coverage, actual color maxima, the
initializer and all coefficient/control positions are checked. Array hashes
use compact ASCII JSON with `separators=(",", ":")` and sorted object keys;
the arrays contain integers in their defined order.

## Controller evidence

For `rho=2^47`, `B=rho^8807` and the **new** three-anchor complemented `K`,
both modular evaluations give:

| Modulus | B | K | H = 1 + B K + B² |
| ---: | ---: | ---: | ---: |
| 47 | 12 | 46 | 39 |
| 8807 | 2677 | 7695 | 6181 |
| 1012691 | 959313 | 26931 | 1009404 |

Route A applies dense Horner evaluation to the full coefficient array at
`rho^(-1)` and uses the reciprocal formula for K. Route B expands the
selector labels and every control directly into positive powers of 2; it
does not use the coefficient array or modular reciprocals. Both share the
reconstructed tile table. As an additional check, the full integer K is
built and reduced modulo all three moduli, as are the full integers B and H.

The prime certificate exhausts trial divisors through
`floor(sqrt(1012691))=1006`. The preceding candidates `101269*m+1` for
`m=5,6,7,8,9` have least factors `2,5,2,3,2`, respectively. The first passing
prime in the requested interval `5 <= m <= 205` occurs at `m=10`; no claim
about the later candidates is needed or made.

With `kappa=lambda-1=1012690`, the additional residues are

```text
B² mod lambda           = 511101 != 1
B^kappa mod lambda²     = 285921151559
                        = 1 + lambda*282338
0 < 282338 < lambda
```

Thus `v_lambda(B^kappa-1)=1`. All three H residues are nonzero.
The verifier also trial-divides `7,17,23,37,47,8807,178481`, proves
`2^23-1=47*178481`, `4403=7*17*37`, and
`lcm(23,4403)=101269`. Proper-divisor tests prove the orders of 2 modulo
47 and 8807 are exactly 23 and 4403. The checked equalities
`gcd(d,23)=gcd(d,4403)=1` give those same orders for B.
Their B² residues are 3 and 6238, respectively. Consequently Pc3 and the
source proof's stated radix-only unit/order facts hold for this precise K.

## Four exact integers and mask checks

Byte counts and hashes below use **minimal unsigned big-endian encoding**,
with no prefix, delimiter or length field. The integers themselves are
constructed in memory from the complete finite formulas.

| Constant | Bits | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| beta | 413929 | 51742 | `98212faf6e2c10c56518b7ff24535a136e04ceb80276d8c617178e1b7753d510` |
| K | 415904 | 51988 | `fa8d378af9a7dde45d710cb4480636a3ab2f5ad4e53210fd68da6fe6b55ab03b` |
| MC | 413929 | 51742 | `f9d3e993386834f3e57b964481c32bb0928645524f089dda517c64fb5fcfcd3f` |
| MF_source | 413930 | 51742 | `fe0075a416f8bea9d12cdac4d7090ad15e0a22e1ad52704880878f2d0bab6f3e` |

The total is **207214 bytes**. Against the maintained radix55 raw lengths
`60549+60837+60549+60549=242484`, this is 35270 fewer bytes. This comparison
is of the four integers' raw binary size, not rendered-page size, proof
complexity, polynomial degree, variable count or global minimality.

Additional exact results are:

- 982 physical positions, including both zero-coefficient dummies;
  980 nonzero coefficients out of 3297.
- Coefficient sum `3882691076540335`; maximum `17592186044416=2^44`.
- Padding population 872, native-mask population 982, and MC population
  `412947=d-982`.
- `0<DC<B`, `beta>=31` odd, `K>0`,
  `0<MC<beta<MF_source<2*beta`, `0<MF_native<beta`,
  `MC=2 (mod 4)` and `MF_native=4 (mod 8)`.

The explicit tuple is `(beta,K,MC,MF_source)` with
`MF_source=MF_native+beta` exactly once. These checks concern the complete
new masks. They are not claims that arbitrary native convolutions are
globally carry-free.

## Provenance, development correction and limits

The deterministic evidence binds these exact inputs:

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| Pinned radix55 equation.tex | 5195 | `440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff` |
| Complemented three-anchor source proof | 31183 | `ab3211b4d9aa7842531a77fde938092c7d96e5cb8dcfdf94bf2b695e156d1ae2` |
| certify.py | 14683 | `318665c36d7600a99dbddbacca11ef9a2d30f65e04a761efe25d1f3653e662ed` |

The certificate SHA-256 is
`f95746541354778fd4f5942a58c0f11c238388017f55b249ff7ca4760c73ee7b`.
Input changes intentionally change the bindings; a saved receipt applies
only to its listed input versions.

The first development run stopped at an incorrect verifier assertion that
4403 was prime. The assertion was corrected using `4403=7*17*37` and all
three necessary proper-divisor order checks. No certificate was emitted by
that failed run. The final certificate contains only actual passed checks;
this correction revealed no obstruction to Pc3.

This is an executable finite certificate with two distinct modular routes,
not two independent implementations of the entire decoder. It supplies no
new native calibration, full carry proof, Pell converse, syntactic-refutation
bridge, internal-ZFC formalization, consistency decision, global minimum or
main-page release approval. The source proof's mathematical contracts remain
the conditions on using its consequence beyond Pc3.
