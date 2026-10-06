# Airy Asymptotics of Bounded-Indegree Labelled DAGs (OEIS A397711)

**`log a_n = 2n log n − n − κ n^{1/3} + o(n^{1/3})` with `κ = 3ζ/2^{1/3}` and
`−ζ` the largest zero of Ai, for labelled DAGs with every indegree at most
two; the analogue for every fixed indegree bound `c ≥ 2`; a Lambert-W
threshold inverse; through an exact generalized-parking reduction and
Mallein's killed-walk area estimates**

A research article ("Report 157" of a session bundle), built from one
manuscript dated 3 October 2026. Its author line reads "Report 157" and its
PDF author field is empty: it names no person, tool or addressee. The package
carries no "prepared for private review" line, no e-mail address and no
personal data. The delivered README used generic `/tmp/report157-build-*`
example paths for its build commands; they are not reproduced here.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 157 (batch 108) | `Bounded_Indegree_DAGs_Airy_Asymptotics_and_Inverses_Source.zip` (14 files, 13 at the archive root and one in `data/`, no wrapper directory, 640,081 bytes, SHA-256 `8686b71d…a9db989343e`), arrival commit `60f54ea06`; main file `Report157.tex` (897 lines, 15 pp.) | none: the package names no ProveIt commit and cites nothing in the repository | `602e5bd0f` (batch 108) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and nothing in the
repository formalizes DAG counts, parking functions or killed random walks.
No proof uses a computation.

## Trust boundaries

- **What is proved here, self-contained.** The sink inclusion–exclusion
  recurrence (Proposition 2.1), the bound `a_n ≥ n a_{n−1}` (7.1), the
  occupancy count (2.8) and the exact normalization
  `a_n = n!(n−1)! e^n Z_n(q)`, `q_i = log(i/(i−1))` (Proposition 3.1); the
  transfer of homogeneous estimates to the reciprocal potential
  (Lemma 5.1) *given* those estimates; Theorems 1.1–1.3 from the lemma; the
  threshold inverse (Theorem 1.2) from Theorem 1.1 and (7.1).
- **What rests on external results.** The step to
  `a_{n,c} = P_n(g_c(0), …, g_c(n−1))` (2.5) uses the general-vector parking
  identity of Kung and Yan (JCTA 102 (2003), Cor. 5.3, Thm. 5.4), cited with
  the source's sketch. The analytic core uses **Mallein's Lemmas 2.6 and 2.7**
  (Stoch. Proc. Appl. 125 (2015); arXiv:1307.4496v3, equations (2.15) and
  (2.19), pp. 11 and 13), printed as Proposition 4.1: the homogeneous upper
  and lower bounds `−c_A h^{2/3}`, `c_A = ζ/2^{1/3}`, for the area-tilted
  killed walk. **They are an external input, cited and not reproved; nobody in
  this intake verified Mallein's proofs.** What is used of them is stated in
  the next section. The analytic theorems hold modulo these two published
  lemmas.
- **The companion** computes `a_{n,c}` exactly for `n ≤ 100`, `c ≤ 5` and
  checks the identities by independent finite routes (direct graph and
  parking enumeration to `n = 5`, rational Poisson weights to `n = 20`,
  pathwise summation by parts to `n = 9`, the forest case `c = 1`). It proves
  nothing asymptotic.

## What is used of Mallein's lemmas

The write read the two statements in arXiv:1307.4496v3 (the PDF downloaded
on 6 October 2026 has the SHA-256 `a20c5c25…` recorded by the source in
`data/SOURCE_PROVENANCE.json`; journal version and author manuscript not
compared), as the write of `a238873-diagonal-partitions` did for its Part IV.
For a triangular array of independent centred variables with
`E[X_{n,k}²] = σ²_{k/n}`, `σ` continuous and positive (2.12), and a uniform
exponential moment (2.13), Lemma 2.6 (2.15) bounds
`limsup n^{−1/3} log sup_{x∈ℝ} E_x[e^{−(h/n)Σ_{j<n} S_j}; S_j ≥ 0, j ≤ n]`
above by `(α₁/2^{1/3})(h σ_min)^{2/3}`, and Lemma 2.7 (2.19) bounds the
`liminf` of the infimum over starts in `[a n^{1/3}, b n^{1/3}]`, with the
endpoint in `[a′ n^{1/3}, b′ n^{1/3}]`, below by
`(α₁/2^{1/3})(h σ_max)^{2/3}`; `α₁ = −ζ` is the largest zero of Ai. Used:
only these two inequalities, for the homogeneous walk `Poisson(1) − 1`
(`σ ≡ 1`, every exponential moment finite), at fixed tilts `h` and fixed
scaled intervals, restricted to integer starting points. Not used: (2.16),
(2.20) (strip-confined walks) or any time-inhomogeneous case; the
inhomogeneity `q_i ≈ β/i` is handled by fixed homogeneous tilts on the
blocks of a geometric grid (Section 5).

## What it proves

`a_{n,c}` counts simple DAGs on the labelled vertex set `[n]` with every
indegree at most `c` (each graph once, no order weighting); `a_n = a_{n,2}`
is A397711. Statement numbers are the delivered ones.

- **Theorem 1.1 (`bid:thm:main`)**: `log a_n = 2n log n − n − κ n^{1/3} +
  o(n^{1/3})`, `κ = 3ζ/2^{1/3} = 5.567271244467717…`; so
  `a_n^{1/n}/n² → 1/e`.
- **Theorem 1.2 (`bid:thm:inverse`)**: for `N(x) = min{n ≥ 1 : a_n ≥ x}`,
  `y = log x`, `b = y/(2W₀(y/(2√e)))`,
  `N(x) = b + κ b^{1/3}/(2 log b + 1) + o(b^{1/3}/log b)`.
- **Theorem 1.3 (`bid:thm:fixedc`)**: for each fixed `c ≥ 2`,
  `log a_{n,c} = cn log n − [c − 1 + log((c−1)!)] n − κ (c−1)^{2/3} n^{1/3} +
  o(n^{1/3})`.
- **Proposition 2.1 (`bid:prop:sink`)**: `a_{n,c} = Σ_{k=1}^n (−1)^{k+1}
  C(n,k) g_c(n−k)^k a_{n−k,c}`, `g_c(m) = Σ_{j≤c} C(m,j)`.
- **(2.5)** `a_{n,c} = P_n(g_c(0), …, g_c(n−1))` (via Kung–Yan) and the
  occupancy form (2.8).
- **Proposition 3.1 (`bid:prop:normalization`)**: `a_{n,c} = n! e^n (Π d_i)
  Z_n(q)` with `Z_n` a Poisson excursion partition function; for `c = 2`,
  `a_n = n!(n−1)! e^n Z_n(q)`.
- **Proposition 4.1 (`bid:prop:input`)**: Mallein's homogeneous bounds (above).
- **Lemma 5.1 (`bid:lem:transfer`)**: if `q_i ≥ 0` and `i q_i → β > 0`, then
  `log Z_n(q) = −3 c_A β^{2/3} n^{1/3} + o(n^{1/3})`.

Added by the write (6 October 2026), with proofs where any, marked `[write]`:

- **Remark 1.4 (`bid:rem:oeis`)**: the OEIS entry, quoted (next section); its
  upper bound `a(n) ≤ g(n−1)^n` is exponentially loose:
  `log a_n − n log g(n−1) = −(1 − log 2) n − κ n^{1/3} + o(n^{1/3})`.
- **Remark 6.1 (`bid:rem:finite`)**: what the exact counts to `n = 100` can
  and cannot say (section after next).
- **Remark 7.1 (`bid:rem:transseries`)**: the inverse against the transseries
  volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
  with its `κ, d, L` renamed `κ_vol, d_vol, L_vol`. (a) `b` is an
  **instance**, verbatim, of `p0:prop:factorial-core` with
  `(κ_vol, d_vol, L_vol) := (2, −1, y)`: `v = W₀(y/(2√e))`,
  `X = e^{v+1/2} = b`, side condition `w > 0`, slope `2 log b + 1 = F′(b)`.
  (b) `N(x)` *is* the staircase `N_*` of `p0:def:three-inverses`
  (`(a_n)_{n≥1}` is strictly increasing by (7.1)), but **Theorem 1.2 is not an
  instance of `p0:thm:staircase`, only an analogue**: it is proved by a direct
  two-ceiling bracket at the integers, `⌊t_{κ−2ε}⌋ < N(x) ≤ ⌈t_{κ+2ε}⌉` (7.5),
  from two envelopes of `log a_n`, not by inverting an interpolation, and the
  separation condition of `p0:thm:staircase(2)` is not available (no eventual
  exact rounding). (c) The displacement `κ b^{1/3}/F′(b)` equals the first
  term of `p0:eq:operator-series` (`p0:prop:operator-form`) with
  `ερ(t) = −κ t^{1/3}`, formally only; it is not an instance of that formal
  proposition, since the perturbation is known only up to `o(n^{1/3})`.
- **Section 10 (`bid:sec:further`)**: the open questions.
- The status note after the abstract, Section 1.1 (`bid:sec:provenance`:
  provenance, the sources as the write read them, what was checked, relation
  to the repository, collected non-claims, reading conventions), and notes at
  the ends of Sections 4 (Mallein's lemmas), 8 (shipped layout, reruns) and 9
  (the OEIS record and the literature).

## The OEIS entry

The live entry A397711 (revision #9, 12 July 2026, read 6 October 2026; the
revision the source recorded), by Tyler Satchel Orden (5 July 2026), offset 0,
is named

    Number of acyclic digraphs (or DAGs) on n labeled nodes in which every node has in-degree at most 2.

(quoted verbatim). Its model is the report's. Its 17 displayed terms are those
in `data/oeis_prefixes.json`, and its b-file (`n = 0..100`) equals the `c = 2`
column of `data/counts.json` term by term (checked at the write, with the
write's own recurrence code; the entry's Python program, a
composition-by-height formula, agrees for `n ≤ 40`). The entry states no
asymptotic formula; its one inequality,

    a(n) <= (1 + (n-1) + binomial(n-1,2))^n.

is the trivial bound `g(n−1)^n`, which by Theorem 1.1 exceeds `a(n)` by a
factor `exp((1 − log 2) n + κ n^{1/3} + o(n^{1/3}))` (Remark 1.4, with the
two-line proof). The entry's comment on `a(p) mod p` and its conjecture
"a(n) == 1 (mod n) for all odd n >= 3, and a(n) == n/2 + 1 (mod n) for all
even n >= 4" (quoted in full in Remark 1.4) are outside this report; the
write only confirmed that the shipped counts satisfy both congruences for
`3 ≤ n ≤ 100`. Recorded only: **nothing was submitted to the OEIS.**

## The constant κ and the finite data

**The n^{1/3} constant cannot be confirmed from the exact counts to
`n = 100`** (found at intake; Remark 6.1). With
`R_n = log a_n − (2n log n − n) + κ n^{1/3}` (so Theorem 1.1 says
`R_n/n^{1/3} → 0`):

| n | 10 | 25 | 50 | 75 | 100 |
|---|---|---|---|---|---|
| `R_n` | 8.332 | 8.799 | 9.165 | 9.386 | 9.546 |
| `R_n/n^{1/3}` | 3.867 | 3.009 | 2.488 | 2.226 | 2.057 |
| `n^{−1/3} log Z_n` (limit `−κ = −5.5673`) | −2.561 | −3.189 | −3.579 | −3.778 | −3.907 |

`R_n` contains `log(2π) = 1.838` from Stirling's formula and an unknown,
unproved lower-order part of `log Z_n`; the table is not evidence for `κ`.
Least-squares fits of the exact `log Z_n` over all integers of the windows
`[20,100]`, `[40,100]`, `[60,100]` (50-digit arithmetic) give the coefficient
of `n^{1/3}` as −5.502, −5.506, −5.509 with the basis `{n^{1/3}, log n, 1}`,
and −5.515, −5.534, −5.542 with `n^{−1/3}` added: all above `−κ`, by 1.2 %
down to 0.5 %. These fits presuppose an expansion form that is not proved, so
they are consistent with `κ` only under that assumption and confirm nothing;
their `log n` coefficient (0.46 to 0.56) is unstable.

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- Logarithmic asymptotics only: no ratio equivalent, power prefactor,
  amplitude, `O(log n)` remainder or all-orders expansion.
- No uniformity in growing `c`; constants and onsets may depend on `c`.
- The inverse: growing permitted error, no eventual exact rounding, no
  additive `o(1)` error, no onset, no certified finite-input bracket.
- The unweighted labelled model, not Chen–Pearl's order-weighted one; `c = 1`
  is the forest case `(n+1)^{n−1}`, with no Airy claim.
- Exact enumeration (Allen et al.; Steinsky), the parking identity (Kung–Yan)
  and the homogeneous Airy estimates (Mallein) are prior inputs; no mechanism
  and no graph-to-parking bijection is claimed as new.
- Steinsky 2003 was read at abstract level only ("important unresolved
  priority limitation", `data/SOURCE_PROVENANCE.json`), with no assertion that it lacks an asymptotic; the
  literature search was bounded.
- Finite checks prove nothing asymptotic; PDF byte identity is
  toolchain-specific.

The write adds: the finite data neither confirm nor refute `κ`; the instance
statements of Remark 7.1 concern the Lambert core only.

## Further questions

Section 10 of the article (`bid:sec:further`) states every unproved claim as
an open question with its source, sketch and what is missing (Vladimir's
standing rule of 4 October 2026). **Nothing in the source was found to be
wrong**, at intake or at the write.

1. **The remainder below `n^{1/3}`** (`bid:q:remainder`; source Section 9,
   "The remaining analytic target"): log term, prefactor, amplitude, an
   `O(log n)` remainder; with the finite-data caveat above.
2. **Growing indegree bounds** (`bid:q:uniform`).
3. **Effective onsets and a certified inverse** (`bid:q:effective`): explicit
   onsets, certified brackets, exact rounding.
4. **The literature boundary** (`bid:q:literature`): Steinsky's full text
   (read neither by the source nor by the write) and a wider search.
5. **Exact Airy amplitudes** (`bid:q:amplitude`; an intake suggestion, not a
   claim of the source): whether the methods of `a082161-airy-amplitudes` give
   a power prefactor and constant for A397711.

## Checks made at intake

- At placement (batch-108 dossier, 6 October 2026; Windows, Python 3.14.4):
  the 10 staged files other than `README.md` and `article.tex` are
  byte-identical to the archive, and so were the staged `Report157.tex` and
  README; `SHA256SUMS` 13/13. The dossier read the manuscript in full, found
  no error and rechecked the key steps by hand (sink recurrence,
  normalization by summation by parts, block comparisons, the two grid
  identities, order of limits, the Brownian eigenvalue `−ζ h^{2/3}/2^{1/3}`,
  the forced terminal descent with probability exactly `e^{−L_n}`, the algebra
  of Theorem 1.3, the inverse), all modulo Mallein. On copies:
  `counts --max-n 100 --max-c 5` reproduced `counts.json`; `verify` refuses on
  Windows (no `O_NOFOLLOW`), and with only its input reader replaced by a plain
  read (an intake helper, not shipped) reproduced `finite_checks.json` byte for
  byte; `threshold --value 1000` gave `first_n` 5; of 34 companion tests 3
  failed and 4 errored, all on the POSIX output guard, 14 skipped as
  POSIX-only; 10 of 11 release tests errored (`os.mkfifo`). No failure is
  mathematical.
- At the write (6 October 2026; same machine): the proofs rechecked line by
  line (also the grid bounds, the interval containments (5.16)–(5.18), the
  initial segment, the increments (6.3) and the expansion of Theorem 1.3); no
  error found. Mallein's two lemmas read (above). The OEIS entry, b-file and
  mirror file fetched (still revision #9). Counts recomputed by independent
  code (b-file equal to `n = 100`; forest formula for `c = 1`; `a_n ≥ n a_{n−1}`
  for `n ≤ 100`). On a fresh extraction of the archive: `SHA256SUMS` 13/13,
  `counts` equal to `counts.json` after converting line endings, `threshold
  --value 1000 --c 2 --max-n 100` gives 5. The finite-data table and fits
  above (mpmath).
- Sources read by the write: the OEIS entry and b-file; Mallein,
  arXiv:1307.4496v3, pp. 11 and 13; the transseries volume
  (`p0:def:core`, `p0:prop:factorial-core`, `p0:def:three-inverses`,
  `p0:thm:staircase`, `p0:prop:operator-form`); the neighbouring reports
  below. Not read by the write: Steinsky, Allen et al., Kung–Yan, Yan,
  Chen–Pearl, Yin (what the source read is fingerprinted in
  `data/SOURCE_PROVENANCE.json`).

## Relation to the repository

**Formal status.** No statement of this report is formalized, and no Lean or
Rocq development in the repository concerns DAG counts, parking functions or
killed random walks. Placement in the collection confers no formal status.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):

- `a082161-airy-amplitudes`: stretched exponentials `e^{3z n^{1/3}}` with the
  **same Airy zero** `z = −ζ` (relaxed and compacted trees, minimal acyclic
  automata), with positive amplitudes and expansions to every fixed order.
  Its `n^{1/3}` coefficient is `3z = −3ζ`, against `−κ = −3ζ/2^{1/3}` here;
  the constant its Parts I, II and IV call `a = 2^{−1/3} z` is `−c_A` here.
  Its data file `data/48-dfa-A331120.seq` (an OEIS snapshot) cites Priez's
  enumeration of minimal acyclic automata "via generalized parking
  functions"; this report uses the generalized parking functions of Kung and
  Yan, while a082161's own proofs use none. This report reaches none of its
  precision (Question 5).
- `a238873-diagonal-partitions`, Part IV (bundle Report 160): the **same
  Mallein Lemmas 2.6 and 2.7**, (2.15) and (2.19), for the `n^{1/6}` Airy term
  of superdiagonal partitions, with the walk `1 − Geom(1/2)` (`σ² = 2`,
  multiplier 1) where this report has `Poisson(1) − 1` (`σ² = 1`, multiplier
  `2^{−1/3}`, the one in `c_A`); its tilt `q` is `h` here. Both apply the
  lemmas only at fixed tilts and fixed scaled intervals; this report
  blockwise on a geometric grid, a238873 with one tilt sequence `q_m → b`.
- Further afield: `a182220-source-boundary` counts *extensional* acyclic
  digraphs, a different class; `a089479-fixed-permanent-matrices` cites the
  unbounded labelled DAG count A003024. Neither treats indegree bounds.

Reciprocal see-also notes for a082161 and a238873 are proposed separately
(not applied by this write).

**The transseries volume.** `b` is an instance of `p0:prop:factorial-core`;
Theorem 1.2 is an analogue of `p0:thm:staircase` only (Remark 7.1). No
novelty is claimed for the inversion.

**Stale claims.** Before batch 108 no file of the repository named A397711 or
bounded-indegree DAGs; the source made no claim about the repository.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `c` (indegree bound) against `c_A` and the
constants `C_r`, `C_{T,r,q}`; `ζ`, `κ` against a082161's `z` and `a` and the
volume's `κ_vol`; `N(x)` (threshold) against the grid horizon `N`; `b`
(inverse base) against the preferences `b_i` and the interval `[a,b]`; `q_i`
(potential), `h` (tilt) against a238873's tilt `q`; `d_i`, `u_i`, `L_n`
against `d_vol`, `L_vol`; `r, ρ, γ, D(r)`; `K_{m,h}`, `J` (both the endpoint
set and the number of blocks, as in the source), `I_j`. No symbol was renamed
in the source text; `κ_vol`, `d_vol`, `L_vol` are the write's names for the
volume's symbols.

## Labels

Every label carries the prefix `bid:` (none existed in the repository). The
manuscript's 76 labels (`eq:` 59, `sec:` 9, `thm:` 3, `prop:` 3, `lem:` 1,
`rem:` 1) were prefixed before anything cited them, and the 58 references to
them updated. The write added 10: `bid:rem:oeis`, `bid:sec:provenance`,
`bid:rem:finite`, `bid:rem:transseries`, `bid:sec:further`, and the questions
`bid:q:remainder`, `bid:q:uniform`, `bid:q:effective`, `bid:q:literature`,
`bid:q:amplitude`. The report has 86 labels; builds of the delivered text and
of this one give all 76 delivered labels the same numbers (aux files
compared). The added remarks are the last statements of their sections, the
added section follows the last delivered one, and the added displays are
unnumbered.

## Files

```text
README.md                      this guide (replaces the delivery README)
article.tex                    the report (delivered Report157.tex; labels prefixed, [write] additions)
article.pdf                    compiled report, 20 pages
code/companion.py              bounded exact counts and finite checks, CLI (delivered at the root)
code/test_companion.py         34 companion tests (delivered at the root)
code/build_pdf.py              deterministic PDF build (delivered at the root)
code/make_zip.py               allowlist-verified source ZIP (delivered at the root)
code/release_tools.py          descriptor-pinned output helpers (delivered at the root)
code/test_release.py           11 tests of the release tools (delivered at the root)
data/SOURCE_PROVENANCE.json    sources, inspection scopes, SHA-256 fingerprints (delivered at the root)
data/counts.json               a_{n,c} for 0 <= n <= 100, 1 <= c <= 5 (delivered at the root)
data/finite_checks.json        full verification output (delivered at the root)
data/oeis_prefixes.json        the 17 displayed A397711 terms and snapshot data (delivered data/)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report157.pdf` (the delivered 15-page PDF, 396,926 bytes); `SHA256SUMS`
(1,063 bytes, 13 entries, verified at placement and at the write; repository
policy ships no checksum manifests); and the delivery `README.md` (10,368
bytes), staged at placement and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.**
`companion.py` reads `data/oeis_prefixes.json` beside itself (in the shipped
layout that would be `code/data/`, which does not exist);
`test_companion.py` reads `counts.json` and `finite_checks.json` beside
itself; `build_pdf.py` compiles `Report157.tex`; `make_zip.py` checks a closed
allowlist of the delivered names (`Report157.pdf`, `counts.json`, …) against
`SHA256SUMS`, neither of which is shipped. Section 8 of the article speaks of
"the PDF", "the README" and "the release manifest" of the delivery. The output
helpers require POSIX (`O_NOFOLLOW`, `O_DIRECTORY`, hard links, `os.mkfifo`).
So nothing runs from the shipped names; use the routes below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Bounded_Indegree_DAGs_Airy_Asymptotics_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 8686b71deb0de00402b5d0bda2ea066bd185d231ffbc5d12a282ea9db989343e, 640,081 bytes
mkdir "$T/pkg" && cd "$T/pkg" && unzip -q ../a.zip     # 13 files at the root, one in data/
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only. Never run anything in the
repository.

**Route A, delivered layout** (as the delivery README gives it):

```sh
cd "$T/pkg"
sha256sum -c SHA256SUMS
python3 -B companion.py counts --max-n 100 --max-c 5 > replay_counts.out        # compare with counts.json
python3 -B companion.py verify --max-n 100 --max-c 5 --rational-to 20 --enumerate-to 5 --parking-to 5 --path-to 9 > replay_checks.out   # compare with finite_checks.json (POSIX)
python3 -B companion.py threshold --value 1000 --c 2 --max-n 100               # first_n 5
python3 -B -m unittest -v test_companion
python3 -O -B -m unittest -v test_companion
```

On Windows (intake, 6 October 2026) the checksum check, `counts` (equal after
converting CRLF line endings) and `threshold` were run at the write; `verify`
refuses there (its input reader needs `O_NOFOLLOW`), and the dossier
reproduced `finite_checks.json` byte for byte only with that reader replaced
by a plain read; the unit tests fail or skip only on POSIX output guards (3
failures, 4 errors, 14 skipped of 34). The release tests
(`python3 -B -m unittest -v test_release`), `build_pdf.py --output-dir` and
`make_zip.py --output` (each refusing existing destinations) need POSIX and
the delivering TeX Live and were not run by the intake.

**Route B, from the shipped files, any OS** (rebuild the delivered layout;
tested at the write: `counts` equal to `counts.json` after converting line
endings, threshold 5):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a397711-bounded-indegree-dags
B=$(mktemp -d); mkdir "$B/data"; cd "$B"
cp "$R/code/companion.py" "$R/code/test_companion.py" .
cp "$R/data/counts.json" "$R/data/finite_checks.json" .
cp "$R/data/oeis_prefixes.json" data/
python3 -B companion.py counts --max-n 100 --max-c 5 > replay_counts.out
python3 -B companion.py threshold --value 1000 --c 2 --max-n 100
```

Use `py` where `python3` is not on the path.

## Build the PDF

pdfLaTeX (fontenc, lmodern, amsmath, amssymb, amsthm, mathtools, geometry,
booktabs, longtable, array, microtype, hyperref); the bibliography is
embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026: 20
pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. The delivered source builds the same way to 15 pages, also
without warnings. The article keeps the delivered preamble lines that
suppress PDF dates and trailer identifiers; the delivered byte-identity
claims apply to `Report157.tex` under the delivering toolchain (pdfTeX
1.40.26, TeX Live 2025/dev/Debian), not to this build.

## From the delivery README

The delivery README (replaced by this guide) summarized the results as above;
listed the package (15-page PDF, LaTeX source, companion, tests, tables,
provenance, build and release helpers, `SHA256SUMS`); gave the replay commands
of Route A, the threshold example (value 1000, `c = 2`, `first_n` 5) and the
companion's bounds (`n ≤ 100`, `1 ≤ c ≤ 8`, rational checks to 25, direct
enumeration to 5, pathwise checks to 9, thresholds up to `10^1000`); counted
the shipped verification (30 graph and 30 parking comparisons exhausting
59,810 pair-state assignments and 3,035,961 preference words, 105 occupancy
comparisons, 34,590 pathwise checks, 50 Catalan checks, 101 forest values, 500
extension checks, 404 monotonicity values, the 17 OEIS terms); said "The
companion suite has 34 tests, and the release suite has 11 tests; both run
normally and under Python `-O`" (on its Linux host); described the
no-clobber output, PDF build and ZIP guarantees and their limits ("they do
not create a general operating-system sandbox"); and said that no external
publication, OEIS editing or author contact is part of the package.

## Rights

Repository contents are MIT-0. The article and the frozen data quote OEIS
terms and text of A397711; OEIS content is published by The OEIS Foundation
Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and those terms remain
under that licence. No third-party PDF is shipped. Nothing was submitted to
the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A397711 (revision #9); Allen et al.,
  JAIR 59 (2017), Thm. 18; Steinsky, Soft Computing 7 (2003) (abstract only);
  Kung and Yan, JCTA 102 (2003), Cor. 5.3, Thm. 5.4; Yan's parking-function
  survey (2015); Mallein, SPA 125 (2015), arXiv:1307.4496v3, Lemmas 2.6–2.7;
  Chen and Pearl, AISTATS 2014; Yin, AofA 2022.
- Batch 108 of `docs/incoming`, bundle Report 157; arrival `60f54ea06`,
  placement `602e5bd0f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report157.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
