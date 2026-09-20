# An ordinal Chomp transition at 2

A computer-assisted counterexample to winner stability and to the
minimal-transition question.

Research report, September 20, 2026. This directory is a merge of two
independently produced reports; see **Provenance** below.

## Result

For the numerical semigroup S = <4,5,6>, ordered by x <=_S y iff y-x is
in S, Chomp is a second-player win at exponent 1 but a first-player win
at every ordinal exponent >= 2. The least winning opening is
omega*4 + 4. Thus ch({4,5,6}) = 2.

The same holds, with the same least winning opening, for
S' = <4,6,9>: ch({4,6,9}) = 2. That second semigroup is now a theorem in
its own right (Theorem 1.2), not a corollary, and it carries two
certificates, one per convention.

Two open items in the literature are settled:

- **Conjecture 4.1** of Fabián Rivero Herrera, *A poset game in
  submonoids of additively indecomposable ordinals*, arXiv:2504.07317v1
  (April 9, 2025) — the **winner-stability** assertion — is refuted.
- **Question 4.6** of the same author's *Hanf numbers for poset games*,
  arXiv:2504.07317v3 (January 5, 2026), credited in that revision to
  Ignacio García-Marco, is answered negatively, already for
  natural-number generators.

The extension uses ordinary ordinal subtraction in its order relation.
At exponent 2 it is the lexicographic, NOT coordinatewise, product.
`omega*4+4` is NOT `4*omega+4`. Only the global least element is
poisoned; higher block bottoms are playable. These conventions are
essential to the result.

## Provenance

This report merges two independently produced research reports:

- `ordinal-chomp-transition-at-two` (September 20, 2026, prepared with
  ChatGPT in response to a research request) — headline result
  <4,5,6>, plus a second certificate for <4,6,9>. This is the spine.
- `ordinal-chomp-winner-stability` (September 19, 2026, prepared for
  Vladimir Reshetnikov) — <4,6,9> alone, in the poisoned-board
  convention.

The theorem the two share, ch({4,6,9}) = 2 with least winning opening
omega*4+4, was proved by the **same argument** in both: the same order
decomposition, the same three-block detector, and a finite certificate
over the same 17 gap ideals. A cell-by-cell comparison confirms the two
certificates record the same 253 rows, agreeing in all 4301 truncated
entries and all 4301 untruncated values once the column permutation and
the convention shift are applied. There is one proof here, run on two
semigroups, and it is given once. Material that genuinely differed is
kept from both and is marked in the article.

## Read

Open `ordinal_chomp_counterexample.pdf`. Its companion LaTeX source is
`ordinal_chomp_counterexample.tex`.

The proof has three parts:

1. A mathematical finite-window recurrence for truncated Grundy profiles.
2. An exact finite-state certificate, including a repeated COMPLETE state.
3. An order decomposition and explicit response procedures showing that
   omega*4 + 4 wins. The responses need only finite game searches.

The smaller certificate has nine gap-tail shapes, seven rows of memory,
387 entries, and an exact state equality at steps 43 and 51, implying
period 8 for the truncated row vectors from row 36 onward. The larger
has 17 gap ideals, eleven rows of memory, 4301 entries, an exact state
equality at 237 and 265, and period 28 from row 226; the poisoned
verifier also certifies that 226 is the *earliest* onset for period 28,
by checking that row 225 differs from row 253. The claim is NOT that the
untruncated Grundy numbers are eventually periodic.

Two sufficient criteria for the mechanism are stated and both are kept:
Proposition 3.5 (incomparability assumed, spectrum hypothesis bundled)
and Proposition 3.6, the diamond-atom criterion, whose hypotheses are
weaker and which derives incomparability from atomicity. Likewise two
descriptions of the winning responses are kept: the general three-phase
invariant argument of Section 7, which names no ordinal moves, and the
block-by-block catalogue of Section 8.10, which names them.

## Poisoned and unpoisoned: the one thing to get right

Two conventions for the same boards are in circulation and both appear
in the shipped files. Section 8.4 of the article is the dictionary.

- **Unpoisoned** (the article's spine, and `certificates/s456.json`,
  `certificates/s469.json`): the board is played with its least element
  0 retained. Cutoff K = 2; digit `3` is a SATURATION SYMBOL meaning
  "at least 3," not "exactly 3." Target: g >= 3. Far spectrum {0}.
- **Poisoned** (`certificates/s469_poisoned.json`, ported): the board is
  played with 0 deleted. Digit `2` means "at least 2," not "exactly 2."
  Target: g >= 2. Initial far-prefix set EMPTY.

The two are related by g(Q) = 1 + g(Q minus {0}), so poisoned labels are
unpoisoned labels minus one. The empty far spectrum is NOT a shift: a
poisoned board simply has no move at 0, whereas the unpoisoned move at 0
leaves the empty game of value 0. Both statements say the same thing.

Every count is convention-specific. The poisoned solver memoizes **4346**
finite states; the unpoisoned `independent_check.py` reports **4347**
distinct finite positions for the same semigroup. These do not conflict.
The same applies to 233, 187, 275, 33, and to the 403/4347 pair in the
article's Section 9 table.

**Column order also differs.** `certificates/s469.json` lists the 17 gap
ideals by ascending bit mask; `certificates/s469_poisoned.json` lists
them by cardinality then lexicographically. The article's Table 1
prints both indices with each ideal's mask, and equation (8.11) states
the permutation. `code/verify_poisoned_certificate.py` asserts the
agreement cell by cell on every run, so the two certificates can never
silently drift apart.

## Verify

Python 3.10 or later for the unpoisoned scripts, 3.9 or later for the
poisoned ones; standard library only, no network access. From the
archive root:

```sh
python code/minimal_verifier.py
python code/verify.py
python code/independent_check.py
python code/verify_poisoned_certificate.py
python code/test_poisoned_certificate.py
```

Do not pass `-O` to the minimal verifier: it uses assertions. The other
verifiers use explicit checks unaffected by Python optimization.

`independent_check.py` does not import or use the finite-window
recurrence. It computes exact, untruncated Grundy values by direct
principal-upper-set deletion on finite posets encoded as bit masks.

`verify_poisoned_certificate.py` does not import the generator. It
reconstructs semigroup membership from 4, 6 and 9; enumerates the 17
ideals by `itertools.combinations` rather than bit masks; recomputes
every displayed boundary value by the literal finite-poset mex recursion
with full integer Grundy values; checks 233 literal local residual-poset
identities and then REPLAYS the bounded recurrence from stored transition
indices alone; checks the 187-entry repeated state and the onset
inequality; checks the diamond's option set is exactly {0,1,2}; runs a
purely finite gadget (Section 8.9); cross-checks the unpoisoned
certificate under the column permutation; and prints the certificate's
SHA-256.

The six regression tests include negative controls (deliberately
corrupted labels and transition data must be rejected), the capped-mex
identity over all 256 subsets of {0..7} at five cutoffs, and the general
boundary recurrence on eight numerical semigroups at three cutoffs —
evidence for the general theorem, not just for one semigroup.

Expected summary:

| Semigroup | Convention | Shapes | Entries | Repeated states | Period starts | Period |
|---|---|---:|---:|---:|---:|---:|
| <4,5,6> | unpoisoned | 9 | 387 | 43 = 51 | 36 | 8 |
| <4,6,9> | unpoisoned | 17 | 4301 | 237 = 265 | 226 | 28 |
| <4,6,9> | poisoned | 17 | 4301 | 237 = 265 | 226 (certified earliest) | 28 |

The direct finite audits evaluate 403 and 4347 distinct unpoisoned finite
positions, and 4346 poisoned ones. `verification.txt` records the actual
executed output of all four verifiers; `verification_poisoned.txt`
records the poisoned run alone; `data/s469_poisoned_tests.txt` records
the regression run. Execution used Python 3.14.4; the two source reports
recorded their original runs under Python 3.13.5. No external service,
floating-point calculation, or unverified extrapolation is part of any
certificate.

`verify_poisoned_certificate.py` prints, among other lines:

```text
VERIFIED
Exact finite positions: 4301
Memoized finite states: 4346
Local residual identities: 233
Repeated boundary state: 237 = 265 (187 entries); period 28
All full-ideal labels are 2, meaning Grundy value at least 2.
Cross-checked against the unpoisoned certificate: 4301 cells
SHA-256: f408697a728c12efd4cca15b73d055b3c747a17e5b06a5897969973ceb1697dc
```

That SHA-256 is the digest of `certificates/s469_poisoned.json`, carried
over from the source report and still valid because the file was copied
byte for byte. It stays valid only while the file is preserved exactly;
any reformat, re-indent, key reorder or line-ending change invalidates
it. `make_poisoned_certificate.py` therefore writes with explicit `\n`
line endings, so regeneration on any platform reproduces the same bytes.
Repository-wide `SHA256SUMS.txt` manifests are no longer distributed, so
this is the only per-file integrity claim in the archive.

The independent audits rewrite their own CSV output files. They do not
alter the certificate JSON files.

## Why a finite certificate proves an infinite assertion

The article reduces the winning-move claim to

    g(Ap(S,t) minus {0}) >= 2, for every positive t in S,

equivalently g(Ap(S,t)) >= 3 in the unpoisoned convention. For each gap
ideal C, the certificate records a row for the finite boundary board with
first missing element x and tail x+C. The complete state is an
eleven-row window for <4,6,9> (seven rows for <4,5,6>) together with the
accumulated far spectrum. Its state before computing row 237 is exactly
its state before computing row 265; all 187 entries agree, and every
full-tail coordinate in the initial segment and the cycle is saturated.
Determinism proves the same assertion for all subsequent rows, and the
exceptional positive first moves below the conductor are checked
separately.

The repeated state, together with the proved recurrence, is the crucial
infinite step. **No assertion about an infinite board is inferred merely
from a large finite truncation.** The exact, unbounded Grundy sequence is
not claimed to be eventually periodic; only each fixed bounded profile
is, and separate cutoffs may have different preperiods and periods.

## Rebuild

The second source report shipped a POSIX `build.sh` wrapper; the `Makefile`
targets below replace it, and `build.ps1` covers Windows PowerShell.

```sh
python code/build_certificates.py
python code/make_poisoned_certificate.py
python code/export_poisoned_tables.py
make verify
make test
make pdf
```

On Windows PowerShell, `.\build.ps1` runs the verifiers, the tests and
three pdfLaTeX passes. That wrapper is supplied for convenience; it was
not executed in the Linux environment in which the original
poisoned-convention verification was recorded.

`make pdf` runs pdfLaTeX three times to settle the table of contents and
cross-references. `latexmk -pdf ordinal_chomp_counterexample.tex` works
equally well. A normal TeX Live or MiKTeX installation with newpx, AMS
packages, geometry, microtype, TikZ, tcolorbox, booktabs, longtable,
enumitem, listings, hyperref, and cleveref is sufficient. The
bibliography is embedded in the source; BibTeX is not required. The
source uses the `data/` tables and the minimal verifier listing, so keep
the directory structure intact. No font or image files are distributed.
Recompiling may change the PDF's byte hash because of timestamps and TeX
versions; the JSON certificates are deterministic.

`make verify` runs all four verifiers, `make test` the regression suite,
`make certificates` the two generators and the table exporter, and
`make clean` removes LaTeX build intermediates, not the PDF,
certificates, or verification records.

`build_certificates.py` intentionally uses the documented candidate
repeat indices; the verifier independently confirms that the states there
agree. It is not a search program. `make_poisoned_certificate.py` IS a
search: it keeps a dictionary of complete boundary states, discovers the
first repetition at 237 = 265 rather than being told where it is, and
derives the period onset 226 from it.

## Contents

- `ordinal_chomp_counterexample.tex`, `.pdf`: the article, with complete
  proofs, both block diagrams, both examples, two sufficient criteria,
  two response descriptions, both complete certificate tables, the
  self-contained verifier listing, and the compact checking algorithm.
- `code/minimal_verifier.py`: short self-contained <4,5,6> check.
- `code/verify.py`: generator-based checker for both unpoisoned
  certificates.
- `code/independent_check.py`: independent exact unpoisoned finite-poset
  audit.
- `code/build_certificates.py`: reproducible unpoisoned certificate and
  table generator.
- `code/verify_poisoned_certificate.py`: independent poisoned-convention
  verifier for <4,6,9>, with the cross-check against the unpoisoned
  certificate.
- `code/make_poisoned_certificate.py`: search-based poisoned certificate
  generator.
- `code/test_poisoned_certificate.py`: six regression tests.
- `code/export_poisoned_tables.py`: regenerates the 253-row longtable
  from the poisoned JSON.
- `certificates/s456.json`, `s469.json`: unpoisoned certificates,
  ascending-mask column order.
- `certificates/s469_poisoned.json`: poisoned certificate for <4,6,9>,
  cardinality-then-lex column order. Carries fields the unpoisoned files
  lack: `format`, `conductor`, `frobenius`, `cutoff`, `label_meaning`,
  `convention`, `ideals` as explicit sets, `full_ideal_index`,
  `early_apery_values`, `prefix_low_values`, `window_length`, `period`,
  `period_start`, `transition_recent_indices`, `transition_tail_indices`.
- `data/*_low_rows.csv`: certified unpoisoned low-profile rows.
- `data/*_exact_finite_audit.csv`: untruncated unpoisoned audit values.
- `data/s469_poisoned_boundary_values.csv`: all 4301 exact, untruncated
  poisoned boundary values, wide format, one column per gap ideal.
- `data/s469_poisoned_apery_values.csv`: exact poisoned AND unpoisoned
  Apéry values for all 258 positive semigroup elements through 264,
  including the exceptional parameters 4, 6, 8, 9, 10.
- `data/s469_poisoned_verification.json`: recorded poisoned verification,
  with `certificate_sha256`, `exact_solver_distinct_positions`,
  `local_residual_identities_checked`, `window_entries`,
  `diamond_normal_value`, `finite_analogue_residual_value`, `method`, and
  `formal_proof_assistant_checked: false`.
- `data/s469_poisoned_tests.txt`: recorded regression-test output.
- `data/certificate_table.tex`, `delta_table.tex`: <4,5,6> article tables.
- `data/s469_certificate_tables.tex`: the 253-row <4,6,9> longtable.
- `verification.txt`: actual output of all four verifiers.
- `verification_poisoned.txt`: actual output of the poisoned verifier.
- `Makefile`, `build.ps1`: build and verification commands.

## Verification boundaries and status

The computations establish every finite entry and the complete repeated
states. The proof of the finite-window theorem is what extends this to
all positive Apéry parameters. The game algebra and the response
procedures are what link that universal spectral fact to the infinite
ordinal Chomp game. A direct finite audit alone would replace neither of
the latter two mathematical arguments.

The trust boundary is ordinary mathematical reasoning plus finite exact
integer computations under Python. No floating-point arithmetic, random
search, external solver, or conjectured period is involved. No formal
proof-assistant verification is claimed. The several implementations are
separate implementations of the same finite calculation, not independent
human proofs; "independently" means code-level independence, not an
external human replication.

This is not a peer-reviewed publication and has not been externally
refereed. The latest source located still posed the question. No earlier
resolution was found, but that search is not an exhaustive priority
determination, and priority has not been independently established.

The result does not classify all semigroups, prove global minimality of
these generator sets, produce transitions larger than 2, or settle the
general decidability problem across all ordinal exponents.
