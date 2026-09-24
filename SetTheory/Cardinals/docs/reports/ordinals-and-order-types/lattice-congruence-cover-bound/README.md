# A sharp cover bound for congruences of finite lattices

Research package dated 20 September 2026.

## Read first

- `sharp_cover_bound.pdf`: the 18-page article.
- `sharp_cover_bound.tex`: complete LaTeX source, including bibliography and diagrams.
- `STATUS.md`: the exact claims and their verification status.

The selected target is the informal suggestion immediately after Lemma 4.4,
page 8, of Gábor Czédli, *Accumulation points of congruence densities of finite
lattices*, arXiv:2603.11454v1 (12 March 2026).

The primary result is the following proposed solution, with a complete written
proof. If an n-element finite lattice has an element with at least k upper
covers, k >= 3, then

    |Con(L)| <= 2^(n-k-1).

Equality holds exactly for C_s glued M_k glued C_t, where M_k is the length-two
lattice with k atoms, the chains have s and t elements, and s+t=n-k. The theorem
also holds for lower covers by order duality.

Further results are a sharp nonextremal bound 3*2^(n-k-3), a fan-label ideal-count
refinement, and the skeleton bound 2*t*(max(2,t)+1) when density is at least p
and t=floor(log2(1/p)).

These are AI-assisted research proofs, not independently refereed or formally
verified results. The search did not find a resolution of the stated all-k
suggestion, but it cannot certify priority. Classical congruence tools and known
low-parameter context are explicitly credited.

## Reproduce the exact computations

Python 3.10 or later; standard library only. The recorded run used Python 3.13.
Run from this directory, without Python's `-O` optimization flag:

```sh
python3 code/verify.py --max-n 8 --independent-through 7
python3 code/examples.py
```

Or run `make verify`.

The first command regenerates per-size JSON results. It includes every
isomorphism class of finite lattices with at most eight elements, using natural
labellings; isomorphic natural labellings are NOT deduplicated. The completed
run includes 4,008 lattices, 25,280 congruences, and 6,292 selected upper-cover
fans. It checks the inequalities, collision lemmas, equality characterization,
sharp gap, profile bound, dual bound, and skeleton bound.

On the 371 naturally labelled lattices with at most seven elements, a second
algorithm enumerates every set partition and tests compatibility. It compares
entire congruence sets with the principal-label algorithm.

The example command regenerates eight detailed examples and 35 structured
larger checks, including Boolean lattices up to 32 elements. Those larger tests
are selected examples, not exhaustive enumeration.

An exploratory n=9 exhaustive run timed out before completion. No n=9 PASS
record or n=9 exhaustive claim is included. Raising `--max-n` can sharply
increase execution time. Timing fields are not reproducibility invariants.

## Build the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error sharp_cover_bound.tex
```

Or run `make pdf`. Standard AMS, Latin Modern, TikZ, hyperref, microtype and layout
packages are needed. No external image files, bibliography processor, font files,
or source PDFs are required. `make clean` removes LaTeX intermediates and leaves
the PDF intact.

## Random selection and exclusions

`data/area_selection.json` records one actual draw from a prewritten ordered
list of 80 areas: zero-based index 9, one-based index 10, **Lattice theory**.
`code/select_area.py` used `secrets.randbelow(80)` and refuses to overwrite that
record. The original random outcome is not deterministically reproducible; the
program and saved record make the method and result inspectable. Do not run it
as part of verification.

The user-supplied `manifest(1).tex` was read in full. Its listed research targets
were excluded. It contains no finite-lattice congruence-density cover question.
The original manifest is not copied into this package.

## Package contents

- `code/lattice_tools.py`: natural-poset generation, lattice construction,
  principal-congruence closure, congruence generation, independent partition
  enumeration, and structural recognition.
- `code/verify.py`: exhaustive finite verification.
- `code/examples.py`: exact examples and larger structured cases.
- `code/select_area.py`: the original area-selection script.
- `data/verification_n1.json` through `verification_n8.json`: completed runs.
- `data/verification_summary.json`: aggregate totals.
- `data/verification_stdout.jsonl`: recorded full-run console output.
- `data/examples.json`: cover lists, operation tables, principal labels,
  congruence partitions, and profiles for eight examples.
- `data/structured_checks.json`: 35 larger structured tests.
- `notes/source_audit.md`: source locations, search status, and exclusions.
- `notes/proof_audit.md`: dependencies and delicate steps.

The article's E_6 and E_7 are named `two_label_six_element` and
`three_label_seven_element` in the example data. Its T_3 is `subdivided_M3`.
`Boolean3` means the 8-element Boolean lattice, not a 3-element lattice.
