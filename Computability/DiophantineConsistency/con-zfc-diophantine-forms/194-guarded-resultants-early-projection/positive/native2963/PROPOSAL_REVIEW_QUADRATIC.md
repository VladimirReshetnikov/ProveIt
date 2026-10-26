# Review of the direct quadratic proposals

Reviewed 23 October 2026 after merging wave 7 (`6d375f2d2d`, merge
`d869b0ddbf`). This review concerns ordinary mathematical constructions and
finite released artifacts. It does not upgrade them to an end-to-end Lean
certificate or an exported object-language ZFC proof.

## Recommendation

Switch the next small-nine formalization target from the dense quartic
encoding to the support-aware quadratic family. Retain several evaluator
tradeoffs rather than declaring a single degree/operation optimum. Package
52 provides the best reviewed low-cost nine-variable targets; package 53
provides the lowest-degree reviewed nine-variable target. The shared next
formal milestones should be selective quadratic extraction, sparse signed
borrow normalization, and the sharp near-square finalizer. These are reusable
across the candidates and do not require importing Sun's new integer theorem.

For the first end-to-end replacement, the conservative source packing of 52
has a smaller new arithmetic interface than 53's calibrated two-block
packing. Package 53 is the appropriate subsequent degree target once that
source-to-binomial bridge is checked. Its finalizer is elementary and is
worth formalizing immediately, independently of the choice of source layout.

The current closed executable `ExplicitZFC.expression` remains the checked
baseline. Replacing only its exponent parameter by a new target span would
be invalid: the old master theorem is specialized to its old source code.
The new source needs its own correctness theorem and native-parent binding.

## Nine-variable comparison

All rows below concern **strictly positive** integer coordinates; these are
not unrestricted-integer results. Gate counts charge live binary arithmetic
operations. Fixed coefficient bit size is a separate metric.

| Package / evaluator | Exact degree | Operations | Assessment |
| --- | ---: | ---: | --- |
| 45 multioutput baseline | 129,875,980 | 788 | Superseded as a numerical target |
| 48 uniform, inherited tail | 29,157,244 | 562 | Dominated by 52's lowest-cost point |
| 48 overlap, major2048 tail | 15,534,796 | 655 | Dominated by 52's compromise |
| 51 sparse arithmetic | 33,332,620 | 682 | Dominated by 48 and 52 |
| 52 interior regular | 15,502,748 | 548 | Low-cost frontier |
| 52 interior packed, uniform shift | 10,486,092 | 603 | Useful compromise |
| 52 interior packed, sparse Horner | 10,127,484 | 655 | Lower-degree frontier |
| 53 parity-calibrated sparse | 7,344,328 | 738 | Lowest-degree frontier |

The first three 52 rows are mutually nondominated. Package 53's conservative
three-block alternative is 12,023,320 / 734, dominated by the 52 compromise.
Its calibrated form buys a material degree reduction for a larger evaluator.
The three 52 natural-coordinate circuits cost three additional operations;
53's calibrated natural-coordinate circuit costs six additional operations
(744 total). Domains and coordinate translations must accompany comparisons.

Among the reviewed ten-unrestricted-integer variants, 48 has
39,914,856 / 651, 51 has 54,768,104 / 709, and 53 has
21,111,400 / 659. The 51 point is dominated. The 48 and 53 points trade
operations for degree, subject to the other packages reviewed in parallel.
These branches import Sun's 2026 arithmetic representation theorem; their
present Lean completion burden is larger than the nine-natural route.

## Mathematical audit

Packages 40/43/45 provide the baseline direct quadratic mechanism: use
factorial-weighted complementary coefficients so selected coefficients of a
packed square equal twice the source residuals. Our checked
`QuadraticCoding`, `MultiQuadraticCoding`, and `MultiTargetCarry` already
formalize the full-Sidon, separated-row, dense-half-bias version of that core.
Wave 7 replaces full Sidon separation by isolation of the actual source
support, and permits row intervals to overlap away from selected targets.
The general proof is valid: enumerate all supported complementary terms
against every quadratic expansion monomial; no unintended term may hit a
selected target. Injectivity of the complementary exponents also prevents a
hidden number-of-rows factor in coefficient bounds.

**48.** Its 71 supported monomials are isolated against all 528 padded
quadratic pairs using weights of maximum 179. The overlap layout has final
target 5775. The universal major2048 proof supplies both the upper radical
gap and a separate lower separation bound before extracting square tests.
Its corrected padding is `2*P*(P+R)+1`; omitting the 2 changes the claimed
exact degree by cancellation. The auxiliary degree graph computes
`D^16 * Final`, not `Final`. Since `D` is a nonzero polynomial, the degree
subtraction is legitimate, but that graph must not be advertised as the
primary evaluator. The reviewed formulas and finite identity checker agree.
No new mathematical gap was found. The long rational-remainder and radical
error estimates are a larger Lean task than 53's majorant identity.

**51.** Its packed successor translation keeps the raw positive parent and
uses `(1+g+ell)^2`; it must not be mixed with the shifted-parent coefficients
used by other adapters. The source proof covers the weaker soundness bound
`g < 4*b*B^W` before decoding, and the stronger completeness bound required
by the actual Jones theorem. Its ten-integer separator `(1,b,b*K)` is not a
generic radical-combining theorem: it uses coprimality and the exact Pell
remainders, including a separate `b=1` bootstrap. The argument addresses that
exception and the potentially zero two-root sum. No new gap was found, but
its nine-variable point is numerically dominated and its integer separator
would add square-class arithmetic formalization.

**53.** The actual source is the original package31 positive parent shifted
coordinatewise by one. Package45 differs in row 15 by
`-beta*(x_J+1)`; the checker explicitly reconstructs and verifies this
transport difference instead of mixing recipes. Its code has maximum input
weight 183, final target 5190, and 136 supported complementary terms. The
checker verifies all 71,808 term/expansion interactions and reconstructs the
22 target identities exactly. The leading complementary coefficient is 2,
so its evaluation is positive before assuming the outer equation.

Sparse padding puts one bit at each target rather than a dense half-base
background. This needs a new signed-borrow theorem: if `|h_i| < B/8`, every
incoming borrow is -1 or 0, and the target digit
`(2*h_i + 1 + borrow) mod B` avoids `B-2` exactly when `h_i=0`.
The argument handles negative residuals; simply treating the formal signed
coefficients as ordinary nonnegative digits would be unsound.

The calibrated rank is
`R=L^2+(S+T)*L+(L-1-S)`, where `L=2*b*B^5741`.
The ratio threshold is the **different** integer
`N=2^16012040*B^2966`. Under the proved `S+T<L`, popcount gives
`v_2(choose(2R,R)) = log2(L)+popcount(T)+1-carries(S,T)`.
With `b=2^k`, `B=2^(2134940+2k)`, the no-carry threshold equals
`2*log2(N)` exactly. The proof establishes `R,N>=8`, `b<=R,N`, and positivity
unconditionally; only afterwards does ratio soundness recover binary `b`
and the weaker cap `g<4*b*B^183`. Thus the source-to-ratio bootstrap is not
circular. Every sufficiently large power of two remains available in
completeness; there is no unproved sparse-cofinality step.

Its sharp finalizer uses the exact identity
`S0^2-64*D*F=t0^2*(8*D+1)-64*D>0`, and
`Omega=u*(2*mu-1)`, which never vanishes. The rational signed root sum
cannot vanish because `0<a0<V0^2` and the second radicand is a positive
integer. Squaring then makes both roots rational, hence integral. The
strict root bounds yield a positive offset and recover both `u | v` and
`mu>0`. Conversely the same bounds construct a nonnegative ninth witness.
The builder matches these formulas, including the positive-coordinate
translation of `C`, and the exact degree certificate exposes the leading
cancellation. No new correctness gap was found in this adapter.

## Reproduction and remaining proof boundary

I extracted the original archives from arrival commit `4b4349064a` into
`/tmp/proofs62ff-wave7-review`; the placed trees omit duplicate members and
checksum ledgers and are not complete replay packages. No delivered files
were repaired or regenerated.

* 48: `python3 verify_release.py` passed, including 141 sealed file hashes,
  44 source pins, 26 primary/certificate circuits, and 14 universal polynomial
  identities. Log: `/tmp/proofs62ff-review48.log`.
* 51: `verify_all.py` passed using Python 3.12.13, including native31 and
  package36 tuple regeneration and normal/optimized component checks.
  Log: `/tmp/proofs62ff-review51-py312.log`. Python 3.13 initially failed
  only strict regenerated gzip-byte comparisons, as anticipated by its
  README; no mathematical checker failed. The 3.12 replay required no edits.
* 53: `verify.py` passed all 21 stages, authenticated 279 sealed files, and
  rebuilt 49 artifacts byte-for-byte using its declared NumPy 2.3.5 and
  SymPy 1.14.0 dependencies in a temporary Python 3.12 environment.
  Log: `/tmp/proofs62ff-review53-py312.log`.

These are finite reproduction results. They verify data, bindings, exact
identities, circuit formulas, and degree/count certificates. They do not
prove the unbounded native-window compiler, the literal machine calibration,
the binomial/Pell interfaces, or Con(ZFC) by running examples. Each package
explicitly retains those mathematical dependencies, and none supplies a new
end-to-end Lean or object-language ZFC derivation. In particular the native
31-variable parent still needs a checked connection to the concrete finite
ZFC-refutation predicate before it can replace the current executable route.

## Checked arithmetic follow-up

`Lean/DiophantineConsistency/NearSquareFinalizer.lean` now formalizes the
sharp defect identity, derives the full strict upper-square bound from the
Pell register equations, and proves the one-natural-witness norm equivalence
for arbitrary integer registers satisfying the explicit positivity and
square-bound premises. Its square-extraction proof uses only rational
algebra and rational-square integrality. The checked theorem does not assume
an independence of radical square classes. It supplies the proposed common
tail, while leaving source packing, native-parent calibration, and the
object-language ZFC derivation boundary unchanged.
