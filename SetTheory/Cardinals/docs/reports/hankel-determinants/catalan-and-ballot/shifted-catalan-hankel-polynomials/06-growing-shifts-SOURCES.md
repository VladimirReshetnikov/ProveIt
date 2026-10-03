# Source and comparison audit

Manuscript date: 29 September 2026, Pacific date.

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit inspected:

    1085b506d65e207a05b7e9c861bb1fe88432fe38

Relevant directory (join the two lines without a space):

    SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/
    shifted-catalan-hankel-polynomials/

Combined `article.tex` blob:

    b23831b8f20efab08342b11bb4939809d0a8047e

Directory README blob:

    ce3436af04afdb64c683d9d36be3f0b45c6ccf5e

The GitHub connector was used to inspect the repository tree, the root README,
the relevant report README, selected contiguous ranges of its combined source,
and `05-interior-collision-SOURCES.md`. This was a targeted comparison, not a
complete audit of every repository file or incoming manuscript. The source
reports are unrefereed; formalization claims elsewhere in the repository are not
used as premises here.

### Exact target

The existing Part I coefficient theorem states

    D_N^(m)(a,1) / H_N^(m+1)
      = sum_{k=0}^N binomial(N,k) (N+m+1)_k a^k
                         / [4^k (m+1/2)_k].

That formula is credited as existing and rederived in Section 3. The source's
fixed-parameter asymptotic section explicitly disclaims uniformity when m grows
with N. Its further-research discussion leaves growing-m joint limits open.
The later endpoint-confluence work fixes its endpoint multiplicities and does
not assert uniform constants in them. The later nonendpoint-collision source
notes describe a fixed-degree problem, not the growing-shift problem treated here.

Relevant inspected ranges in the combined source:

- Lines 180–350: normalization, exact coefficient formula, fixed-shift statements.
- Lines 940–1070: exact finite exponential expansions, fixed-parameter asymptotics,
  and the explicit warning that growing m requires another uniform analysis.
- Relevant report README, especially lines 210–410: fixed multiplicity scope,
  remaining growing-m question, and the distinction between the earlier parts.

The present paper specializes to one additional linear factor and resolves an
explicit growing-shift continuation for that family. It does not declare every
extension named by the repository solved. The README and newer continuation
files were not assumed to be perfectly synchronized; the fixed-degree
nonendpoint source notes were checked separately to avoid treating that already
addressed direction as new.

## Public primary literature

### Christian Krattenthaler

*Hankel determinants of linear combinations of moments of orthogonal polynomials,
II*, Ramanujan Journal 61 (2023), 597–627; arXiv:2101.04225.

https://arxiv.org/abs/2101.04225

Role: classical polynomial-modification/Christoffel determinant identity and
orthogonal-polynomial context. The article rederives the one-factor identity in
its own sign and normalization conventions. The paper's public abstract and
metadata were inspected; a requested arXiv PDF fetch did not succeed during this
session. No claim of a complete theorem-by-theorem comparison is made.

### NIST Digital Library of Mathematical Functions

Section 18.5(iii), equation 18.5.7, Jacobi hypergeometric formula.

https://dlmf.nist.gov/18.5.E7

Role: the finite Jacobi series, with parameters alpha = m - 1/2 and beta = 1/2.
The available DLMF mathematical entry was inspected. The manuscript's symbols
v, B, c, and its concentration parameter beta are defined separately; its beta
is not the Jacobi endpoint parameter.

### Holger Dette and William J. Studden

*Some new asymptotic properties for the zeros of Jacobi, Laguerre and Hermite
polynomials*, arXiv:math/9406224 (1994).

https://arxiv.org/abs/math/9406224

Role: prior large-parameter Jacobi-zero asymptotic context, including parameter
regimes that outgrow the degree. The public abstract was inspected; a requested
PDF fetch was unsuccessful. No specialized theorem from that paper is invoked
as an unverified premise. An equivalent transformed zero law in this or later
literature has not been ruled out.

### A. D. Barbour and P. Hall

*On the rate of Poisson convergence*, Mathematical Proceedings of the Cambridge
Philosophical Society 95 (1984), 473–480.

https://doi.org/10.1017/S0305004100061806

Role: the classical Bernoulli-sum Poisson bound used explicitly in Section 10,
with total variation defined as half the l1 distance:

    d_TV(sum Bernoulli(p_j), Poisson(lambda))
      <= (1 - exp(-lambda)) / lambda * sum p_j^2,
    lambda = sum p_j.

The bibliographic record and the standard stated bound were checked through
primary-source search material. The manuscript credits this bound; it is not
presented as an independently discovered ingredient.

### Pierre-Loïc Méliot, Ashkan Nikeghbali, and Gabriele Visentin

*Mod-Poisson approximation schemes and higher-order Chen–Stein inequalities*,
arXiv:2210.13818 (2022).

https://arxiv.org/abs/2210.13818

Role: established higher-order Bernoulli and mod-Poisson approximation context.
The primary abstract was inspected. No specialized assertion from the paper is
required in the new derivations.

## Limits of the literature check

Searches targeted growing Jacobi parameters and inverse zeros, Catalan Hankel
shifts, and higher-order Poisson approximation. They establish relevant prior
mechanisms and make a sweeping novelty claim inappropriate. They do not prove
that an equivalent formula or theorem is absent from the literature. The article
therefore distinguishes an addition relative to the inspected repository from
worldwide first-discovery priority.

The Catalan density, Jacobi representation, Christoffel identity, Bernoulli
factorization mechanism, and generic use of logarithmic cumulant corrections
are not claimed as discoveries. The paper's proof-focused contribution is their
explicit all-aspect-ratio implementation for the specified normalized family,
including finite-parameter bounds, a closed moment law, the sharp comparison
profiles, and the stated uniform prefactor.

No outside PDF, source manuscript, or repository file is redistributed in this
archive. All source links are bibliographic references, not dependency downloads.
