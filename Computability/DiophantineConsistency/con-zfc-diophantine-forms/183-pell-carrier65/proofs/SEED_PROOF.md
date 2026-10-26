# Reverse-discovery digits: a shorter complete mixed-radix seed recipe

Delivery paths: the final page is equation.tex; its numeral is equation/SEED.txt; the coefficient routines are code/coefficients.py, called by verify.py and code/build.py. The old page is sources/CURRENT_P66.tex. Preparatory diagnostic filenames below identify research steps; the final combined metrics are the delivery metrics.

## Scope and novelty boundary

This is a finite representation improvement for the exact four fixed integers
in ProveIt's admissible942 page at commit
`02a78a08603cbae248c19c23a75907c6c6bd6443`. It does not alter the polynomial,
its witness domain, the 430 machine actions, the indexed 942-tile language,
the native proof or any controller condition. It introduces no new unbounded
mathematical assumption. It can therefore be composed with an independently
justified change of the polynomial front.

The repository already explored mixed-radix target streams: its
`research/mixed-radix-bfs-seed/PROOF.md` and README record 397--399-symbol
seeds whose complete printed recipes were 26--35 nonwhite characters longer.
That prior method is explicitly credited. The improvement here is to store
old targets as reverse-discovery distances, making the same final formula
recover active targets, new targets and the unique early halt. It avoids the
earlier separate halt correction and makes a mixed-radix complete recipe
shorter in the measured template. No worldwide priority is asserted.

## A general finite packing lemma

Fix a finite number m of actions and H active-state labels, with labels
0,...,H-1 and halt label H. Let nu_j in {0,1} mark a first discovery and
sigma_j=sum_{k<j}nu_k. A discovery action has target sigma_j+1; a non-discovery
has target in {0,...,sigma_j} or target H. Suppose sigma_m=H-1. Put

    r_j = (sigma_j+2)^(1-nu_j),
    P_j = product_{k<j} r_k.

Here nu_j and r_j are defined for 0<=j<m; sigma_j and P_j are defined for
0<=j<=m, with sigma_0=0 and P_0=1. Define digits by

    d_j = 0                                  if nu_j=1;
    d_j = sigma_j - target_j                  for an old active target;
    d_j = sigma_j + 1                         for the halt target.

Every digit satisfies 0<=d_j<r_j. In the halt case sigma_j<=H-1, so its
digit is at most H and its target will be recovered by reduction modulo H+1.
Let T=sum_{j<m}d_j P_j. Standard mixed-radix induction gives 0<=T<P_m.
For any nonnegative auxiliary field E let Q=T+P_m E. Then

    floor(Q/P_j) mod r_j = d_j.

Indeed, the part from earlier positions is less than P_j; each later term
is divisible by P_j r_j. The extra term P_m E has the same divisibility.
The assertion also holds at a discovery position because r_j=1 and d_j=0.
The auxiliary field is recovered by floor(Q/P_m)=E.

The single target decoder is

    target_j = (sigma_{j+1} - (floor(Q/P_j) mod r_j)) mod (H+1).

There are three exhaustive cases. At a discovery sigma_{j+1}=sigma_j+1
and the extracted digit is zero. At an old active target nu_j=0 and the
subtraction gives the target exactly. At the halt it gives -1, whose least
nonnegative residue modulo H+1 is H. The outer modulo is necessary; in the
actual machine the unique halt is action125, with sigma125=80.

No underlying machine run is needed to evaluate this finite recipe, and no
variable from the Diophantine equation occurs in it.

## Exact specialization

Take m=430 and H=215. The low field N is the unchanged 636-bit merged mask.
Its low 430 bits give nu_j. At bit430+q it contains the exception bit m_q for
the two write/move actions at source state q. Let

    tau_q = sum_{k<q} m_k,
    F_q = 14 + m_q * (D_16(E,tau_q)-14),
    D_b(A,k) = floor(A/b^k) mod b.

Then for j=2q+b, write_j=D_2(F_q,2b) and direction_j=D_2(F_q,2b+1).
These are exactly the old flag formulas. With the unchanged old E, form

    A_new = N + 2^636 * (T + P_430 E).

The fully printed 399-character numeral in mixed_seed.txt defines A_new
using the explicit alphabet 0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz.
Recover N=A_new mod 2^636 and Q=floor(A_new/2^636); the prefix products depend
only on the already recovered discovery bits, so no definition is circular.
The final PDF inlines E=floor(Q/P_430) at its only use.

The entire old 436-character numeral remains in the pinned equation.tex only
as comparison evidence. The new displayed equation reads no old source file,
external table, or data-dependent search.

## Exact verification

verify_seed.py separately decodes the old and new literal numerals and checks
all 430 triples (target,write,direction). It then independently transcribes
the complete admissible942 tile table, requires unique coverage 0..941,
reconstructs both complete Psi specializations, Phi, both masks and K, and
checks the entire four positive integer values and their minimal unsigned
big-endian SHA-256 hashes against the repository's finite certificate.

The four integers have total 94689 bytes, and their hashes are unchanged.
The actual initializer remains tile928=(3,436,4,4), and the unique early halt
remains action125. Deliberately changing the first, middle or final numeral
symbol is rejected. Omitting the outer modulo changes the actual halt to -1
and is rejected. Normal and optimized Python runs produce identical receipts.
These finite checks establish literal equality; they are not represented as
a bounded test of the unbounded consistency theorem.

## Measured complete specification

The diagnostic page retains the exact old fifteen-variable front, fonts,
fixed tile table, Psi recipe, footer and page format. It changes only the
decoder and its literal, with an inlined E field and the explicit convention
"Empty sums/products are 0/1." Its final target formula uses both pairs of
parentheses around the nested remainder, avoiding a precedence ambiguity.

| Metric | Pinned baseline | Reverse-discovery recipe |
|---|---:|---:|
| Packed numeral bits | 2594 | 2373 |
| Base62 numeral characters | 436 | 399 |
| Entire coefficient recipe, nonwhite pdftotext -raw characters | 1992 | 1973 |
| Entire diagnostic page, same character convention | 2671 | 2652 |
| Standalone TeX bytes | 5025 | 5012 |
| Pages | 1 | 1 |

Thus the full recipe, including all decoding overhead, is 19 characters
shorter, and the TeX source is 13 bytes shorter. This is a modest measured
gain, not a change in arithmetic circuit operations, total degree, coefficient
height or minimum raw coefficient storage. The diagnostic PDF renders without
overfull boxes; one actual full-page visual review found no overlap or clipping.
The final combined page should be measured and visually reviewed afresh.

### Combined 14-variable page

The completed composition in `combined/equation.tex` replaces the P66 front
by the separately proved first-Pell carrier P65 and makes the prefix endpoint
`j<=430` explicit. Its measured coefficient section has1980 nonwhite
characters, versus1992 in the pinned baseline. The entire page has2655
nonwhite characters versus2671, and its standalone source is5014 bytes
versus5025. Both render to one Letter page at the same fonts. Word counts
increase from738 to743; this is not a word-count reduction. Local rebuilt
PDF bytes increase from159737 to160419. The four unchanged integer ports
still total94689 bytes.

`build_combined.py` creates the page and all four minimal unsigned big-endian
port files. It checks the complete extracted399-character PDF numeral,
one-page count, absence of overfull boxes and every pinned port hash. A fresh
actual full-page image inspection of this combined endpoint passed.
`verify_seed.py` also checks the scalar interface beta>=31, K>0 and
0<MC<beta<MF_source<2beta required by the new arithmetic proof.

## Sources and license

All paths below are in VladimirReshetnikov/ProveIt at the pinned commit.

- Computability/DiophantineConsistency/equation.tex
- Computability/DiophantineConsistency/research/admissible942-independent/certificate.json
- Computability/DiophantineConsistency/candidates/one-page-admissible942/README.md
- Computability/DiophantineConsistency/research/mixed-radix-bfs-seed/PROOF.md
- Computability/DiophantineConsistency/research/mixed-radix-bfs-seed/README.md
- Computability/DiophantineConsistency/SEED_COMPRESSION54.md
- Computability/DiophantineConsistency/SEED_PREDICTORS54.md

The repository root LICENSE is the MIT No Attribution License, copyright2026
ProveIt Contributors. The new proof, finite verifier and reverse-discovery
packing construction were prepared in this session with AI assistance.
