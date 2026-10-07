# Source and claim audit

Date: 7 October 2026.

## Sources actually used

**W. T. Gowers, A new proof of Szemerédi's theorem**, GAFA 11 (2001), 465–588,
DOI 10.1007/s00039-001-0332-9. Section 17, especially Lemma 17.1 and
Proposition 17.2, provides the selected-Fourier-square/phase-removal interface.
The printed page 578 was visually inspected. Its proposition prints degree
`k`, while its proof uses the degree `k+1` polarization. The selected sum is
normalized by `N^(k+2)`, giving cube dimension `d=k+1`.

PDF used:
https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

**Jonathan Tidor, Quantitative bounds for the U^4-inverse theorem over low
characteristic finite fields**, Discrete Analysis 2022:14, 17 pp,
DOI 10.19086/da.38591, arXiv:2109.13108v2. Definition 3.1 and Propositions
3.4–3.5 establish the nonclassical symmetry criterion in all degrees. At
`d=p+1`, its repeated-variable identity is exactly `B_T=0`. That equivalence
is therefore known, not a new open-problem solution. Lemma 2.1 records the
Tao–Ziegler nonclassical polynomial normal form.

https://arxiv.org/abs/2109.13108

**Terence Tao and Tamar Ziegler, The inverse conjecture for the Gowers norm
over finite fields in low characteristic**, Annals of Combinatorics 16
(2012), 121–188, DOI 10.1007/s00026-011-0124-3, arXiv:1101.1469.
Used for the established nonclassical polynomial framework. The manuscript's
weighted binomial lemma is proved directly rather than treated as a new
classification theorem.

https://arxiv.org/abs/1101.1469

**James Leng, Ashwin Sah, and Mehtaab Sawhney, Improved bounds for Szemerédi's
theorem**, arXiv:2402.17995 (2024). Global context only; not a theorem input.
The present work is not advertised as competing with this global bound.

https://arxiv.org/abs/2402.17995

## Repository interfaces inspected

The repository was read through the GitHub connector. No write was performed.
The inspected Research tree identifier was
`36d278747e85da646cf1df25a5a8a5b957f9d948`. This is a tree identifier, not a
claim that all files in a concurrently changing repository have that commit.

- `Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections17_18.lean`
- `Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md`
- `Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/43-boolean-phase-FORMALIZATION.md`

Source URLs:
https://github.com/VladimirReshetnikov/ProveIt/blob/main/Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections17_18.lean
https://github.com/VladimirReshetnikov/ProveIt/tree/main/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements

The formal source explicitly uses degree `k+1` and factorial-invertibility
hypotheses. Its numbered catalogue propositions are Prop-valued definitions;
their presence is not evidence of completed proofs. The source-43 plan uses
a different homogeneous-tensor interface and explicitly warns against
confusing it with `IsMultilinear`, which permits lower-order terms. It also
records that circle-valued nonclassical primitives cannot be replaced by
F_p-valued primitives without loss.

The existing research compilation contains Boolean integration, cubic
alternating-rank repair, and other energy/phase refinements. This package
acknowledges that overlap. It does not claim those Boolean results as new,
and does not use their unverified proofs as dependencies.

## Claim separation

1. **Established background:** ordinary Gowers norms/Gowers–Cauchy–Schwarz;
   nonclassical symmetry/integration; elementary alternating linear algebra.
2. **Written proofs derived here:** finite-cover polarization on arbitrary
   finite abelian groups; twisted quotient-profile comparison; first-obstruction
   minimum abelian kernel, classification and counting; simultaneous-family
   minimum cover; joint repair frontier; rank-only energy and radical-coordinate
   stabilization.
3. **Exact computer-assisted result:** the 289-coefficient ternary Laurent
   census and the upper bound 1099/2187 obtained from it. Every underlying cube
   is rebuilt with integers. The Python program remains part of the trust base.
4. **Exact regression checks:** 39 primitive cases and 25,334 finite differences.
   These check examples of general written proofs, not all primes or dimensions.
5. **Conjecture only:** the sharp ternary maximum 11/27. The constant function
   proves the lower bound, and a 30-start numerical search supports it; neither
   is an upper-bound proof.
6. **Not claimed:** a global Szemerédi improvement, a general low-characteristic
   symmetrization theorem, a complete inverse theorem, or any new Lean build.

## Scope of novelty assessment

The exact combined cover-optimality and quotient-profile formulations were
not located in the primary sources and repository interfaces inspected.
The assessment is not exhaustive. General polynomial-cover constructions,
polynomial maps on finite abelian groups, and extension-theoretic descriptions
may contain equivalent statements in other language. The article provides
proofs independently of that priority question and is intended for mathematical
and bibliographic review before publication or formal-ledger integration.

## Delicate points specifically checked

- All-slot symmetry is assumed; symmetry only in derivative directions is not enough.
- The energy is normalized by |G|^(d+1) in unnormalized cube sums.
- The multiplicative derivative uses conjugation, never division by the function.
- The gauge sign is `E_T(f) = E_(T-S)(f * e(-P))` when `Delta^d P=S`.
- General covers need not be p-groups in the lower bound; equality forces the
  displayed p-group structure.
- Minimum covers are classified as covers over V with unlabelled kernels;
  primitives themselves are not being counted.
- Common-cover energy bounds preserve each quantity in the mean over cosets,
  not necessarily simultaneously on one coset.
- The phase-only Laurent bound extends to the whole unit polydisc by norm
  convexity, not by numerical sampling.
- The ternary threshold uses a strict inequality; equality is not classified.
