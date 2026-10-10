# Integration notes: Stieltjes convolution calculus

## Baseline and intended placement

This continuation was prepared against `VladimirReshetnikov/ProveIt` commit
`570b0567f311cf1890865065896be2665f469e4f` (10 October 2026). The accompanying patch targets the exact
Git blob of `Analysis/Polylogarithms/docs/manuscript/chapters/07-integration.tex`
at that commit.

A suitable intake location for the complete delivery is:

`Analysis/Polylogarithms/docs/reports/stieltjes-convolution-calculus-2026-10-10/`

For the consolidated manuscript, place the analytic continuation after the
existing integration and parameter-derivative material represented by the
Chapter 7/8 source sequence, `chapters/07-integration.tex` and
`chapters/08-differentiation.tex`. Let the master manuscript assign the final
printed chapter numbers. The main components can be integrated in this order:

1. Shifted Hurwitz convolution, spectral derivatives, and explicitly normalized
   Hadamard finite parts.
2. The periodic distribution formulation, including the delta terms at the
   coincident point, followed by the correction for raw parameter derivatives.
3. Ordinary log-Gamma correlations and their primitives.
4. The complementary positive-moment/Hankel theorem and its fixed-parameter
   large-order asymptotics.

These are proposed insertion points. Existing harmonic derivative ladders,
primitive Dirichlet functional-equation bridges, and rational-grid distribution
results should be cited from the canonical chapters rather than duplicated as
new discoveries.

## Scope of the proposed patch

`proposed_corrections.patch` contains exactly two scoped edits to the baseline
`07-integration.tex`:

- At `integral:neg:psim2`, replace the unconditional requirement of rationally
  independent search atoms by a prescription to remove known dependencies or
  search modulo their known relation space, requiring a nonzero target
  coefficient for an evaluation.
- At `integral:res:hurwitzladder`, state `Re z > 0`, specify the holomorphic
  log-Gamma branch that is real on the positive axis and the principal
  logarithm of `z`, and record absolute local uniform convergence.

The ladder formula itself is correct on the stated half-plane. At `z=-1/2`
its displayed series diverges, because
`zeta(n,1/2)=(2^n-1) zeta(n)`, so omitting a convergence domain is consequential.
The article supplies an independent proof and explicit tail bounds.

## Namespacing before a canonical merge

The delivered article is standalone. Before incorporating its sections into
the consolidated manuscript:

- Prefix its generic labels, such as `thm:fp`, `eq:polygammaFP`, and `sec:loggamma`,
  with a unique namespace such as `sc26:`. Update every matching reference,
  including `ref`, `eqref`, `autoref`, and any cleveref-style reference.
- Check bibliography keys and custom command names for collisions; map them to
  established manuscript conventions or give them the same unique prefix.
- Reuse the manuscript's theorem environments and typography when extracting
  chapter fragments; keep the standalone preamble in the report copy.
- Preserve relative paths to figures and the verification directory, and
  distinguish this article's finite-part distributions from ordinary functions
  and from any pre-existing negative-polygamma notation.

The definitions of the finite part and the local logarithm scale are part of
the theorem statements. In particular, the global convolution identities
contain delta terms even when their restrictions to `0 < a < 1` do not.

## Status of existing candidates

This delivery does not change the following baseline statuses:

| Item | Baseline status and precise locator |
|---|---|
| The stated short `S6` reduction | Conjectural; the present convolution and Hankel theorems do not prove or refute it. |
| The newer frozen `S8` vector | Conjectural: `chapters/04-S8-candidate.tex`, label `s8new:conj:S8`. |
| A different, earlier `S8` vector | Certified false: `chapters/10-discovery.tex`, proposition `research:prop:S8-rejected`. |

The two `S8` vectors are distinct and must retain separate status entries.
A numerical certificate rejecting the earlier vector is not a rejection of
the newer frozen candidate. The present article is a proved continuation;
it does not claim to resolve a matching pre-existing convolution conjecture
or to establish arithmetic independence of the special values.

## Proof and verification boundaries

The analytic results are established by the proofs in
`Stieltjes_Convolution_Calculus.tex`. The finite-part and derivative results
use a specified scale-one local cutoff convention and meromorphic families of
periodic distributions. Ordinary log-Gamma correlations use convergent
integrals. The moment determinant theorem requires `a > 0` and `p > 1`;
its large-`p` asymptotic fixes both `a` and the determinant size. For `0 < a < 1`
the log-spectrum measure is a Hamburger moment measure, since its smallest
support point is negative.

The delivered Python checks and JSON results are high-precision diagnostics,
not interval certificates or proof-assistant formalizations. In particular,
floating-point evaluation of a proven analytic tail bound is not itself a
certified numerical enclosure. Finite Cauchy-Binet sums, independently
computed parameter and spectral derivatives, raw-cutoff quadratures, and
complex ladder examples provide complementary implementation checks.

The uncompensated Stieltjes derivative generating function is entire: its
polynomial factor cancels the apparent pole. The compensated moment generating
function has its pole at the stated positive parameter. Later tuple products
in the exact determinant expansion can coincide, so equal exponential bases
should be grouped when describing the complete ordered expansion.

## Exact source identity and patch validation

The following hashes refer to the exact UTF-8 Git-blob bytes, including the
final newline.

| Object | Value |
|---|---|
| Baseline repository commit | `570b0567f311cf1890865065896be2665f469e4f` |
| Original file size | `67247` bytes |
| Original Git blob SHA-1 | `52c8487a618429fb8a0cd3978705614b9a193505` |
| Original SHA-256 | `999856e86b27c93f716d9106bdedca30b677584e1373595fbf5357ece0d740f9` |
| Patched file size | `67823` bytes |
| Patched Git blob SHA-1 | `af6ee043b407a7e60c44ae8b639618262dde1a27` |
| Patched SHA-256 | `94937557989eca0d048a14add88c8bfc15ef0abdc2ff1835f462cf6280127614` |
| Patch SHA-256 | `44ae902728867e339e6a6af9d74acebd1ee7105622ece2ac7042fba9942b927d` |

Validation was performed on a temporary scratch copy containing the exact
original Git blob:

1. `git apply --check proposed_corrections.patch` completed with exit code 0.
2. Applying the patch to that temporary copy completed with exit code 0.
3. The applied bytes matched the independently constructed expected result
   byte for byte, including the patched SHA-256 above.

The patch is provided for review and later integration. The standalone article
and the repository snapshot were not modified by these validation operations.
