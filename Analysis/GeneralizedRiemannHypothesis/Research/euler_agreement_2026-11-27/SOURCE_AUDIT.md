# Source comparison and mathematical status

Date: 27 November 2026.

Repository: VladimirReshetnikov/ProveIt.

Commit: `6b034b74a8224c893e7e83127f33cd1a6958785d`.

## Review scope

The review used the directory and article READMEs; all 19 substantive article
section sources were retrieved for topic searches; the recovery section and
the relevant source mechanism were read in detail. All 42 current Research
packet READMEs were checked. The full TeX of the eight relevant current Euler
matching papers was inspected for statements and exponent assumptions.
This is a topic-focused review, not independent validation of all 997 results
counted in the article's own inventory.

The exact source pin is essential: later repository commits may merge or
supersede these results.

## Direct article precedents

Source: `Analysis/GeneralizedRiemannHypothesis/Article/sections/rec.tex`.

- `rec:sec:qmatch` and `rec:thm:qmatch`: elementary quadratic character packets.
- `rec:sec:omatch`: odd-prime-exponent matching.
- `rec:lem:otrace`: one trace decides the Euler polynomial at prime exponent.
- `rec:lem:oradon`: anchored-projection inequality for elementary abelian groups.
- `rec:thm:odigit`, `rec:thm:osmall`, `rec:thm:olevel`: exact prime-exponent results.
- `rec:lem:gram` and `rec:thm:ofinite`: smoothed GRH prime transfer.
- `rec:sec:open`: explicit question about composite exponent.

Pinned URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/6b034b74a8224c893e7e83127f33cd1a6958785d/Analysis/GeneralizedRiemannHypothesis/Article/sections/rec.tex

## Full-source comparison with unmerged Euler papers

Paths below are relative to `Analysis/GeneralizedRiemannHypothesis/Research/`.

| Source | Inspected scope and open extension |
|---|---|
| `cubic_quintic_euler_agreement/paper.tex` | Prime exponent; explicitly asks for composite exponent. |
| `grh_cubic_matching_and_precision_2026-11-27/papers/cubic.tex` | Exponent three. |
| `odd_euler_agreement/paper.tex` | Prime exponent; asks for prime-power exponent. |
| `odd_prime_euler_agreement/paper.tex` | Prime exponent; asks for exponent p^j or mixed exponents. |
| `odd_prime_euler_agreement_2/paper.tex` | Elementary prime exponent; asks for composite orders. |
| `odd_prime_euler_packets/odd_prime_euler_packets.tex` | Explains the prime-exponent trace restriction; asks for composite analogues. |
| `prime_exponent_euler_agreement/prime_packet.tex` | Asks for exponent ell^m and all power traces. |
| `prime_order_euler_agreement/paper.tex` | Prime exponent; asks for composite exponent. |

## Claims of contribution

The new repository-relative results are:

1. The exact minimum disagreement density for every cyclic group and every
   packet size, including arbitrary composite exponent, its sharp saturation
   threshold, and explicit attaining packets.
2. The resulting exact minimum over all cyclic families and its
   exp(-EulerGamma)/log(log k) asymptotic, including attainment with primitive
   factors of a common prime conductor.
3. The corrected projection for arbitrary finite abelian p-groups, the sharp
   coefficient-sensitive mass bound, all equality cases including the actual
   torsion-lift condition, the saturation floor and threshold, all saturated
   equality cases, and the exact minima at prime-power packet sizes.
4. The sharp cyclic prime-window density certificate via its exact Fourier norm.

The divisor-trace criterion is elementary finite Fourier algebra and is
provided as the correct formulation, not promoted as a deep new result.

## Credited antecedents and limitations

- Minimum-volume trades are classical. The signed-marginal lemma is proved
  in full and credited to this established principle. See Ghorbani, Kamali,
  Khosrovshahi and Krotov, EJC 27(1) (2020), P1.29:
  https://arxiv.org/abs/1810.02296
- Finite-group uncertainty is established background; see Meshulam:
  https://arxiv.org/abs/math/0312407
- Martin and Walji study finite-group trace agreement and refined local-global
  questions, primarily for irreducible representations. Their stated problem
  is relevant context; the present objective uses whole local polynomials of
  reducible abelian packets with fixed total degree:
  https://doi.org/10.4064/aa170120-1-5
- The global cyclic asymptotic uses classical Mertens and prime number
  theorems. A primary source explicitly recording the Mertens product is
  Keliher and Lee, Integers 24A (2024), A12, Eq. (3):
  https://math.colgate.edu/~integers/a12Proc23/a12Proc23.pdf
- The smoothed prime estimate and the general O(m^2 log^2 Q) distinguishing
  scale are inherited. A simple anchored trace already gives that scale;
  it is not claimed as a new general detection exponent.
- The source RH/Dirichlet-GRH input is accompanied by Sutherland's public
  verification report at https://math.mit.edu/~drew/shortgrh/ . Those upstream
  builds were not replayed here, and the new proofs are not Lean-verified.

No bounded search can certify worldwide priority. The mathematical claims
are supported by the supplied proofs; the novelty claim is limited to a
concrete advance over the inspected source statements.
