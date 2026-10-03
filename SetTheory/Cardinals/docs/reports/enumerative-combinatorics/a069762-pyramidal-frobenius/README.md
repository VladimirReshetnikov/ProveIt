# Three Consecutive Square-Pyramidal Numbers

**Exact Frobenius formulas, gap laws, and algebraic inversion (OEIS A069762)**

A research report dated 1 October 2026, built from one manuscript (author
line: "Research report prepared for Vladimir Reshetnikov"; AI-assisted,
although the manuscript does not say so).

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 75, manuscript 02 | `OEIS_Pyramidal_Frobenius.zip`, arrival commit `4b874cea0` (main file `article.tex`; its PDF not shipped) | `29aca108e` (1 October 2026), named in the bibliography entry `proveit` and in the delivery README as a "root-tree snapshot"; it is a commit, an ancestor of the placement commit | `6ea60e367` | the whole report |

**Status:** AI-assisted (not stated in the manuscript), unrefereed, not
formalized. Exact finite
checks corroborate the formulas; they do not replace the proofs in the text.

## What it proves

`s_n = n(n+1)(2n+1)/6`, and `F_n` is the Frobenius number of
`<s_n, s_{n+1}, s_{n+2}>` (OEIS A069762). Put
`h_n = (0,3,2,3,0,5)[n mod 6]`. The report proves:

- **The exact formula.** For every `n >= 2`,
  `F_n = [4n^5 + 32n^4 + (101-10h)n^3 + (175-45h)n^2 + (102-65h)n - 36 - 30h]/36 + ε_n`
  with `h = h_n`, where `ε_n = 0` except at `n = 2, 3, 5, 11, 17, 23`
  (corrections 10, 40, 315, 1612, 3135, 2400). The cutoff 24 is sharp and the
  least eventual period is six. In particular `F_n = n^5/9 + 8n^4/9 + O(n^3)`,
  with the first oscillating term at order `n^3`.
- An explicit Apéry normal form after two gcd reductions, controlled by a
  relation `kC - ℓA = 5B` with `k, ℓ <= 6`; constructive membership and
  representation certificates.
- The exact genus (no exceptions) and the symmetry classification.
- Exact quasipolynomials for every fixed gap-power sum (Apéry–Bernoulli
  formula); the first moment in closed form (Appendix A).
- A general transfer theorem from limits of normalized Apéry sets to gap
  measures, and, as its application here, the triangular law: a uniform gap
  divided by `F_n` tends to the density `2(1-x)` on `[0,1]` with `O(1/n)`
  error in the distribution function.
- The minimal generating-function denominator
  `(1-x)^6 (1+x)^4 (1+x+x^2)^4` and a minimal eventual recurrence of order 18
  (valid from `n = 42`).
- A convergent Puiseux inverse of each residue-class polynomial, with
  vanishing coefficients `c_{5j} = 0`, a conservative uniform convergence
  region (`t > 100`), and residue-aware discrete rounding for
  `y >= F_29 = 2940909`.

## What is not claimed

- **Eventual quasipolynomiality is not new:** it is the theorem of Roune and
  Woods (at most three generators) and of Shen (polynomial-parametric), as
  the manuscript says (Section 1). The claim is the explicit formula, the
  normal form and their consequences for this family. Three consecutive
  squares and cubes (Lepilov–O'Rourke–Swanson) and triangular and
  tetrahedral numbers (Robles-Pérez–Rosales) are the literature context.
- Priority is not certified: the OEIS entry had no formula, and a bounded
  primary-source search found none. That is a limited observation.
- The "scope of the claim" box on the title page: this settles no named
  conjecture; A069762's definition is not labelled a conjecture.
- The inversion material is an **instance of repository results**, with no
  novelty claimed for the method. Theorem 10.1 is the Lagrange–Bürmann
  theorem `p0:thm:LB` of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`,
  and Corollary 10.3 is part (4), the residue-class case, of that volume's
  `p0:thm:staircase` with modulus 6 (written with floors and a maximum
  rather than ceilings and a minimum). Two dated `[write]` notes in
  Section 10 say so. The convergence region (Proposition 10.2) is the
  report's own.
- Finite checks prove nothing about all `n`; no proof assistant was run.
- The Section 12 research directions are questions, not results.
- `oeis_submission.txt` is a draft and was **not submitted** to the OEIS.

## Relation to the repository

**Formal status.** No ProveIt Lean or Rocq file treats Frobenius numbers or
numerical semigroups (searched for "Frobenius number", "numerical
semigroup", `NumericalSemigroup`, `frobeniusNumber` in tracked `.lean` and
`.v` files on 2 October 2026). **No statement of this report is
formalized**, and its place in the collection gives it no formal status. The
generic staircase lemmas it instantiates are formalized as
`Fabius.staircase_ceil`, `Fabius.staircase_separation` and
`Fabius.isLeast_residue_class` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; those
concern an arbitrary monotone interpolation, not `F_n`.

**Neighbouring reports.**
`enumerative-combinatorics/numerical-semigroup-leaf-types` is the
collection's other numerical-semigroup report: the type of leaves in the
numerical-semigroup tree (a genus-34 counterexample to a conjecture of
Chappelon, Ramírez Alfonsín and Stamate, and the order of the maximal leaf
type). `automata-and-formal-languages/constrained-crossover-closure` uses
only the two-generator Frobenius number as a lemma. Neither treats a
parametric three-generator family, and no theorem is shared. (These
pointers are made here only; those reports are not edited by this write.)

## Labels

Every label carries the prefix `pyf:`. The manuscript's 104 labels were
prefixed before anything cited them (26 `\ref` and 68 `\eqref` updated); no
label was added, so the count is 104. Five dated `[write]` notes were added
(Section 1: provenance, pin, formal status, neighbours; Section 10: two
instance notes; Section 11: rerun; Appendix C: package as shipped), with two
bibliography entries (`pyf-tai`, `pyf-leaf`). No statement, proof or number
of the manuscript was changed.

## Files

```text
README.md                          this guide (replaces the delivery README)
article.tex                        the report (delivered under the same name)
article.pdf                        compiled report, 21 pages
oeis_submission.txt                draft OEIS formula/recurrence text, NOT submitted, as delivered
code/verify.py                     exact formula, genus, membership, inverse; Dijkstra and DP checks; writes data.csv
code/derive_moments.py             symbolic gap-moment polynomials for a given power (imports verify)
data/data.csv                      n = 2..1000: generators, F_n, genus, symmetry defect (CRLF)
data/verification.txt              recorded output of verify.py --symbolic
data/moment1.json                  first gap-power-sum polynomials, six residue classes
data/moment1_verification.txt      recorded output of derive_moments.py --power 1
data/moment2.json                  second gap-power-sum polynomials
data/moment2_verification.txt      recorded output of derive_moments.py --power 2
data/rational_gf.json              numerator (degree 41) and denominator (degree 18) of sum F_n x^n
data/requirements.txt              sympy==1.14.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. The delivered PDF is not shipped. The
delivered package was flat; placement split it into `code/` and `data/`.
`data/data.csv` has CRLF line endings as delivered (Python's `csv` writer)
and keeps them through a `-text` line in
`SetTheory/Cardinals/.gitattributes`. No delivered program writes
`rational_gf.json`; on 2 October 2026 its series was checked here against
`F_n` for `2 <= n < 200` (agreement). Delivered text that names the flat
layout or unshipped files: the article's Section 11 and Appendix C (commands
`python verify.py --symbolic` and the compiled PDF; dated notes added) and
`oeis_submission.txt` (refers to `rational_gf.json` beside it and to the
manuscript by title).

**Discrepancy with the placement record.** The placement commit
`6ea60e367` says that manuscripts 02 and 05 "record no revision". Manuscript
02 does record one: its bibliography entry `proveit` (and its delivery
README) names `29aca108ed25d714f31b1316512777fbbdc8e006`, called a
"root-tree" identifier there, which is the commit `29aca108e`. The table
above uses it as the pin. The sentence in Section 1 saying that the snapshot
is recorded in the bibliography is therefore correct as delivered.

## Rerun the checks (on a scratch copy)

`verify.py` writes `data.csv` into `--out-dir` (default: its own
directory, i.e. `code/`), and `derive_moments.py` imports `verify` from its
own directory. Neither reads anything from `data/`. Run on a copy so that no
shipped file is touched (Git Bash, from this directory):

```sh
R=$(mktemp -d) && cp code/*.py "$R" && cd "$R"
uv run --no-project python verify.py --out-dir . > verify_basic.txt                 # standard library only
uv run --no-project --with sympy==1.14.0 python verify.py --symbolic --out-dir . > verification.txt
uv run --no-project --with sympy==1.14.0 python derive_moments.py --power 1 --output moment1.json > moment1_verification.txt
uv run --no-project --with sympy==1.14.0 python derive_moments.py --power 2 --output moment2.json > moment2_verification.txt
```

Then compare with `data/` modulo line endings (on Windows, redirected
stdout and `Path.write_text` produce CRLF). On 2 October 2026 these four
commands took 3 s, 6 s, 2 s and 4 s here (at intake, under load, the first
three took 25 s, 78 s and 41 s): all checks passed; `data.csv` came out
byte-identical; `verification.txt` identical apart from its seconds line;
`moment1.json`, `moment2.json` and both `*_verification.txt` identical
modulo line endings.

## Build the PDF

pdfLaTeX with Latin Modern, amsmath, amsthm, mathtools, booktabs, tabularx,
longtable, microtype, enumitem, fancyhdr and hyperref. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory: 21 pages, no errors, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations, no overfull or underfull boxes. (The delivered source
built to 20 pages with the same clean log.)

## Provenance

- OEIS A069762 (inspected 1 October 2026); Lepilov–O'Rourke–Swanson,
  Semigroup Forum 91 (2015); Robles-Pérez–Rosales, J. Number Theory 186
  (2018); Roune–Woods, EJC 22(2) (2015) P2.36; Shen, arXiv:1510.01349 v3.
- Repository input: a scoped reading of the root README and the
  `Combinatorics` directory at `29aca108e`, used only as a methodological
  model; no ProveIt theorem is a hypothesis of any result here.
- Batch 75 of `docs/incoming`, manuscript 02; arrival `4b874cea0`, placement
  `6ea60e367`, written in the batch-75 write phase (2 October 2026).
