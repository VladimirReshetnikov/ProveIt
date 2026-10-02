# Sources and retrieval scope

Prepared 2 October 2026. These are links and a source-use account, not copies
of third-party full texts.

## OEIS

- https://oeis.org/A336293 — original counting sequence and its forward expansion
- https://oeis.org/A395976 — reduced rational numerators; late quotient conjecture
- https://oeis.org/A395977 — reduced rational denominators

The accessible indexed A395976 body identifies the quotient and displays

d_j ~ j^(j-1/2)/(sqrt(pi) 2^(2j-3/2) exp(j-2)),

attributed to Vaclav Kotesovec, 21 May 2026. Its displayed forward example has
d0=1, d1=55/24 and d2=2581/1152. The entry also asks about positivity beyond
index five. Indexed content was retrieved on 2 October 2026, approximately
07:31–07:32 UTC. The search metadata described a crawl about four months old.
It cannot exclude an unindexed later revision.

Direct entry, .seq and b-file retrieval attempts failed (403 responses or
cache misses). There is no raw OEIS b-file validation in this package.
The exact coefficient checks derive from the counting definition and the
saddle transform; they are not a comparison to an independently downloaded
complete OEIS data file.

## Primary analytic references

- NIST DLMF 10.40: https://dlmf.nist.gov/10.40
  Fixed-order modified Bessel asymptotics, sectorial error control, and the
  mixed I0 K0 product expansion (10.40.6).
- NIST DLMF 5.9.2: https://dlmf.nist.gov/5.9.E2
  Principal-branch reciprocal-Gamma Hankel integral.
- NIST DLMF 5.11.8: https://dlmf.nist.gov/5.11.E8
  Shifted logarithmic Gamma expansion with Bernoulli polynomials.
- Michael Borinsky, Generating asymptotics for factorially divergent sequences,
  Electronic Journal of Combinatorics 25(4) (2018), Paper 4.1:
  https://arxiv.org/html/1603.01236v4
  Proposition 22 supplies the product derivation. Theorem 35 supplies the
  composition rule. Its real-beta scope includes beta=0, explicitly justified
  by Lemma 37. These are established methods, not new general theory here.

The report's Gaussian membership and integration estimates are proved before
using the fixed-parameter composition rule to identify the answer. The
reciprocal-Gamma expression is a finite-order coefficient generator; it is
not an origin Taylor coefficient of a multivalued function or a claim that
an infinite Gamma sum converges.

## Bounded overlap review

The overlap review inspected 185 individually retrieved complete TeX or
Markdown texts from the ProveIt repository at commit
4b874cea0012c51a6841ad9c58f6e20fa57c71da. Selected generating-function and
asymptotic texts, related factorial and Borel material, and the canonical
transseries volumes were included. No proof of the target quotient conjecture
was located in that inspected set. Inspected Bessel/Laguerre passages concerned
other problems. Unread files, historical versions and binary-only material
are outside that scope. This does not establish worldwide originality.
