# Source audit and scope

Audit date: 7 October 2026. This is a limited primary-source and repository
inspection, not an exhaustive novelty search.

## Repository snapshot

The formal comparison and Boolean-plan comparison use commit
`b9760ed931282087ee57cb1ffb66dc66e40ee47b` in
`VladimirReshetnikov/ProveIt`.

| Inspected source | Role in this contribution |
|---|---|
| `Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections17_18.lean` | Exact hypotheses and degree in the corrected Proposition 17.2. The file's blob is `18495f50475835ca1c497d85b0052215f865b8ca`. |
| `Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md` | Research-index review for previously covered themes. The initial index read used the live default branch; this was not a complete read of every indexed manuscript. |
| `Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/43-boolean-phase-FORMALIZATION.md` | Comparison with prior Boolean integration and obstruction work. Its inspected blob is `c2c551f44ae04462f6e315aa81160ba1ee7517dd`. |

Pinned formal source:
https://github.com/VladimirReshetnikov/ProveIt/blob/b9760ed931282087ee57cb1ffb66dc66e40ee47b/Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections17_18.lean

Pinned Boolean plan:
https://github.com/VladimirReshetnikov/ProveIt/blob/b9760ed931282087ee57cb1ffb66dc66e40ee47b/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/43-boolean-phase-FORMALIZATION.md

The Section 17 declaration concerns a cyclic prime field, an explicit
factorial-invertibility assumption, a multiaffine selector, and an energy
conclusion. Its phase degree is k+1. The new paper instead concerns already
produced circle-valued polynomial correlations on F_p^n. It does not silently
remove the hypotheses of the existing predicate. No repository or ledger
mutation was performed.

The research index and targeted repository searches did not reveal a
critical-depth sine-ratio/list-minimality theorem under the chosen terminology.
A terminology search is not a proof of absence. Prior manuscripts may contain
related observations in different language.

## Primary mathematical sources

### Gowers (2001)

W. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA 11 (2001), 465–588.
DOI: 10.1007/s00039-001-0332-9.

https://link.springer.com/article/10.1007/s00039-001-0332-9

Used for the phase-removal/density-increment context. The corrected repository
predicate, not the OCR transcription alone, is the formal comparison point.
No new global quantitative Szemerédi conclusion follows from the new local
conversion theorem by itself.

### Berger–Sah–Sawhney–Tidor (2022)

A. Berger, A. Sah, M. Sawhney and J. Tidor, *Non-classical polynomials and the
inverse theorem*, Math. Proc. Cambridge Philos. Soc. 173 (2022), 525–537.
DOI: 10.1017/S0305004121000682. arXiv:2107.07495.

https://arxiv.org/abs/2107.07495
https://arxiv.org/pdf/2107.07495

The Section 3 proof of Theorem 1.1, on PDF page 4 (zero-based page 3), explicitly
obtains epsilon/sqrt(p) after converting a degree-p nonclassical phase. That
page was inspected as a PDF image as well as parsed text. The present paper
replaces this conversion factor by the exact
sin(pi/p)/(p sin(pi/p^2)). Their qualitative classical U^(p+1) inverse theorem
is prior work; no claim is made to have discovered it.

Their higher-degree counterexamples are also important: the current result
cannot be iterated freely to remove every depth at a fixed high degree.

### Tao–Ziegler and Tao's notes

T. Tao and T. Ziegler, *The inverse conjecture for the Gowers norm over finite
fields in low characteristic*, Ann. Comb. 16 (2012), 121–188.
DOI: 10.1007/s00026-011-0124-3. arXiv:1101.1469.

https://arxiv.org/abs/1101.1469
https://link.springer.com/article/10.1007/s00026-011-0124-3

T. Tao, *Some notes on “non-classical” polynomials in finite characteristic*,
author's notes, 13 November 2008.

https://terrytao.wordpress.com/2008/11/13/some-notes-on-non-classical-polynomials-in-finite-characteristic/

Nonclassical polynomial degree/depth and multiplication-by-p degree lowering
are established background. The article supplies elementary proofs of the
particular algebraic facts it needs. The existence or quantitative strength of
a general nonclassical inverse theorem is treated as an external input.

### 2026 scope check

T. Milo and G. Moshkovitz, *Nearly-polynomial inverse theorem for the U^d norm
in degree d+1*, arXiv:2603.16836v2, 30 April 2026.

https://arxiv.org/abs/2603.16836v2
https://arxiv.org/html/2603.16836v2

The authors' stated regime is finite fields of non-small characteristic and
polynomial inputs of controlled degree. This is not the same question as the
present sharp lower-depth conversion. The paper is included as a scope check,
not as an input to the proofs or evidence of a new general inverse bound.

## Claim ledger

| Claim | Status in the delivered work |
|---|---|
| Multiplication by p lowers additive degree by p-1 | Standard background; a self-contained operator proof is supplied. |
| Top residue is linear at d=1+a(p-1) | Derived self-contained from degree lowering. |
| Exact sine-ratio norm comparison | Proved in the manuscript, including sharpness in all dimensions. |
| Classification of phase-endpoint maximizers | Proved using root-polygon equality and conditional averages. |
| Exactly p fixed candidates are necessary and sufficient | Proved; lower bound uses cyclotomic independence. |
| Quantitative frame stability | Proved; coefficient is explicit but not claimed optimal. |
| Square-root stability exponent is optimal | Proved using the invertible score coordinates. |
| Simultaneous aggregate-energy factor c^2 | Proved and sharp; not componentwise. |
| One-pass selector | Implemented and tested in double precision. |
| General noisy-polynomial repair | Not claimed. |
| Improved inverse-function dependence on delta | Not claimed. |
| New global Szemerédi bound or major open-conjecture solution | Not claimed. |
| Lean-kernel verification | Not performed. |
| Publication priority | Not established by this audit. |

No third-party paper PDFs or repository source files are redistributed in the
archive. The archive contains the newly written manuscript, its code, and its
supporting notes and generated checks.
