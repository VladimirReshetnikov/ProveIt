# Calibrated carry thresholds for ZFC consistency

This release specifies fixed Diophantine equations whose lack of solutions,
on their stated domains, is provably equivalent in ZFC by ordinary mathematics
to the inherited syntactic Con(ZFC) predicate. It does not decide consistency,
claim a global simplicity minimum or fewer unknowns, or certify these new
literal equations end-to-end in Lean, Rocq or object-level ZFC.

## Main results

All operation counts charge every live binary addition, subtraction and
multiplication, including scalar multiplication. Fixed leaves and register
reuse are free. Degrees are exact total polynomial degrees.

- Nine positive integers: recommended 564 operations / degree 4,400,764;
  lower degree 598 / 4,399,820; lower cost 490 / 9,461,300.
- Ten unrestricted integers: recommended 554 / 14,699,152;
  lower degree 558 / 14,696,016; lower cost 513 / 25,838,224.
- Fifteen positive integers: new 68 / 101, 70 / 80, 71 / 78,
  72 / 64 and 73 / 62. The 66 / 157 comparison is inherited, not newly invented.
- All four native coefficients are bound together to the inherited complete
  base-2^429959 tuple, totaling 215492 uncompressed bytes. MF_source is
  already shifted. No coefficient port is mixed with an older instance.

The nine-positive family also has separately charged natural-coordinate
translations. It is not silently a nine-unrestricted-integer theorem.
All root graphs and their metric receipts are retained, including dominated
comparison variants. See the report for the full finite-catalogue comparison.

## Read and replay

1. Read `report/report.pdf`; editable TeX is in the same directory.
2. Install Python 3.10+ and the packages in `requirements.txt` in your own
   environment if needed. No package installation is performed by replay.
3. Run `python3 verify_release.py` from any directory. The program validates
   the sealed file set and source identities, makes an isolated temporary
   copy and runs only authored checks. It never executes incoming programs.
4. Run `python3 negative_controls.py` for corruption and optimization rejection.
   The changes occur only in temporary copies.
5. Optional: `python3 rebuild_artifacts.py` regenerates source, packing,
   circuits and fixed leaves in another temporary copy, and checks their
   exact byte identity in the tested environment.

Do not compile TeX, run builders, add files or allow Python bytecode into the
sealed tree before replay: integrity validation intentionally rejects any
extra file. Work in a copy for modifications. The top-level verifier rejects
`-O` and `-OO`, and ignores inherited PYTHONOPTIMIZE for its subprocesses.

For ordinary TeX Live/MiKTeX, compile `report.tex` twice in `report/` or use
`latexmk -pdf`. `report/build.sh` is a fallback for the research Linux setup;
it uses existing fonts/formats and disables shell escape. No TeX cache is
shipped. PDF generation is not needed for mathematical finite replay.

## Exact equation identifiers

The recommended nine-positive graph is
`nine/generated/nine_170_selective12_packed_shifted_quotient2048_positive.json`.
Its degree-oriented alternative is
`nine/generated/nine_170_selective12_packed_quotient2048_positive.json`.
The recommended ten-integer graph is
`integer/generated/sun10_170_selective12_packed_shifted_homogeneous_sparse_popcount_equal.json`.
The recommended short-degree graph is `positive/p72_degree64.json`.
All other letters in the report are polynomial registers, not additional
quantified witnesses. Every JSON declares its ordered variables and domain.

## Layout

- `native/`: whole four-port tuple, formula-based checker, ordinary inherited
  receiver proof, controller/transition data and original notices.
- `source/`: the exact 31-coordinate quadratic parent, twelve-coordinate
  shift, complete positivity proof and sparse-popcount bridge.
- `packing/`: nine literal isolation certificates, elementary proof and
  exhaustive checker; no heuristic optimizer is a proof dependency.
- `nine/`: source-parametric tails, explicit full circuits, derived fixed
  payloads, degree certificates and uniform majorant proof.
- `integer/`: full ten-integer source/tail circuits and fixed leaves,
  conditional equal-weight separator proof and exact-degree checks.
- `positive/`: all six short-frontier circuits, two comparison circuits,
  squared-modulus/minimum proof and independent formula/degree checker.
- `audit/` and `short_audit/`: separately authored arithmetic/circuit audits
  and their receipts.
- `review/`: eight-arrival comparison, intake check results and three later
  status documents, clearly separate from the main construction pin.
- `inherited/`: selected exact ordinary proof sources and pinned arithmetic
  interfaces. Their programs are not run by the release verifier.

## Provenance and formalization boundary

The main input pin is ProveIt commit
4b4349064a750ba6347293b55874a7f92abdd0db, with common prior construction
baseline 124c07c0b77a9e20e84676514d8b1ff78536ea3f. All eight input ZIP Git
blobs and CRCs were checked at intake. The full ZIPs are deliberately omitted.
`PROVENANCE.json` separates genuine retained direct-file Git blob checks
from selected archive-member SHA-256 checks. The replay does not pretend to
recompute omitted archive hashes. The manifest is integrity metadata, not
an external signature; record the outer ZIP digest via a trusted channel.

A later, separately pinned d2f19e4d5cc4030f60049333285eea86a1ef401c snapshot
reports a closed executable actual-ZFC equation and generic simultaneous
quadratic/carry lemmas. Its P67 compiler integration, smaller closed quadratic
adapter and internal object-level consistency iff remain distinct unfinished
boundaries. This release does not claim those later checks certify its own
new coefficient-specific circuits, and does not rerun the later Lean builds.

The elementary new proofs plus the explicitly inherited native/compiler,
K215/refutation, Jones and Sun theorems give the ordinary mathematical ZFC
proofs claimed. Finite test success alone cannot supply those unbounded
semantic theorems. Read the proof dependencies before quoting a result as
formally kernel-certified.
