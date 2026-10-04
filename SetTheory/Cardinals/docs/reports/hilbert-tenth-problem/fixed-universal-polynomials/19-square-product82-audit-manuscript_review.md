# Independent Report45 mathematical manuscript review

**PASS.** I read the complete reconstructed `Research_Report45.tex`,
including the source definitions, all three residue branches, uniform
bounds, Pell growth and resonance, strict ratio, shared input projection,
matched signs, even-c auxiliary completion, eighteen-witness assembly,
scope, and provenance/replay statements. No mathematical transcription
error or unjustified strengthening of the counterfamily theorem was found.

The reviewed TeX revision has SHA256

    d659f7f565bdbbfab39f8b0fea0d78178e864acceff3227987c2794b768ded46

The article's `source_rows.txt` has SHA256

    385c8c2288257a7bcef3c1562645ed67baa3883a2641e6372cf315a34612c719

All 82 article rows were independently compared as inert data with the
recovered immutable pinned receipt, in exact order. All eight recovered
repository source snapshots independently matched their recorded source
hashes. No upstream code or saved arithmetic schedule was run.

## Resolved clarification

The first revision said that b was an odd power of five and then said
“in particular b≥3.” Being a power of five alone would allow b=1.
The actual inherited compiler also requires 2^b≥16. The article now
explicitly states b∈{5,25,125,...}, cites that radix lower bound and
explains that only odd b≥3 is used in the construction. This was a
clarification of the genuine recipe, not a counterexample or change to
the theorem. The corrected text is included in the hash above.

## Critical checks

- Actual source A denotes Delta, not the Pell parameter; L16 is the
  auxiliary F_aux, distinct from packing F
- The genuine shifted MF is used in the actual M and packed R
- The nonzero-m3 CRT uses valid inverses modulo a power of five and
  produces the required sign and u parity
- The zero-m3 branch uses modulus t/5 and multiplication by five correctly;
  it never inverts a multiple of three
- F and alpha restore the literal C=W+Z; R is computed by the source
- The lower/upper R bounds, p>I, p>t+e and y≥3t are justified uniformly
- The exact resonance and strict ratio give positive eta and zeta
- The positive retained quotient h gives index factor epsilon
- The same rho and sigma restore both main and input root projections;
  the ordinary input is unchanged and delta is a positive integer
- The transport factor also equals epsilon, so the negative pair at
  m3=1 cancels inside the complete paid polynomial
- All constructed c are even; the direct auxiliary index R≡3 mod4
  is sufficient without invoking the review's odd-c sector
- The finalizer is the exact Delta*(P5*Na*Qs−1), with all three factors
  equal to one for the constructed tuples
- p is even while R is odd, and F_aux lies strictly between consecutive
  squares; infinite choices of r give distinct unbounded J
- The empty-set conclusion is stated for the unchanged genuine compiler;
  a different numeral compiler is not ruled out
- Toy mask fixtures and small Pell components are not represented as
  materialized genuine compiler counterexamples
- Recovery text distinguishes immutable source recovery from newly
  reconstructed research files, with fresh hashes and replay evidence

This review concerns mathematical transcription and evidence scope.
PDF rendering, visual inspection, archive reproducibility and the final
release wrapper are checked separately by the release process. Later
layout-only changes may produce a different TeX digest; they must be
identified by the release's own manifest rather than assigned this hash.

The fresh recovered independent checker was run normally and with `-O`
from `/`; the resulting receipts are byte-identical. Its 2,520 outer,
70 residue-control, 18 Pell, five even-c auxiliary, and 288 congruence
counts agree with the article's independent-evidence summary. Its source
dependency is the recovered sibling packet named in the article, with
an optional `--source-root` override for recovery/replay.
