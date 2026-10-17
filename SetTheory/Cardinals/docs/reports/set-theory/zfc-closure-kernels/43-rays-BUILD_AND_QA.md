# Build and verification record

Final report: **28 physical letter pages**, including one cover page and
one contents page. Produced 17 October 2026 (UTC).

## Mathematical review

The normalized integer-ray construction was reviewed independently for:

- uniqueness of normal representatives and literal Extensionality;
- hereditary supports and the exact relative power carrier;
- the full stabilizer-orbit argument for arbitrary fixed capacity k;
- set-sized exact fibers, supported omega closure, and the exact native CP;
- source-covered partial-functional Replacement;
- finite acyclicity together with failure of Foundation;
- relative set-model interpretation, including nonstandard source models;
- the fixed empty-replacement/Pairing equivalence and degenerate cases.

The native calibration was checked as an ordinary ZFC argument.
The bisimulation witness is explicitly an **internal raw set code** in
the starting model, not an arbitrary external relation. The subsequent
well-founded and constructible domains are internally defined and only
then taken as subsets of the external set-sized model domain.

No new proof-assistant theorem or serialized ZFC proof was produced.

## Finite computation

During research:

- Both exact public machine hashes were recomputed.
- The runtime252 blank run was inspected through 100,000,000 literal moves.
- Every one of 8,391 cases was evaluated at all eight stated gaps
  in both the affine and fixed-gap modes.
- Sixteen selected short-gap literal traces reached different complete
  frames; four gap-36 controls reached exact targets.
- Source 35's prior 2,794-move positive check was reproduced.
- The finite support-orbit diagnostics passed for k=1,2,3.

The assembled-package replay used:

~~~sh
python3 -B code/reproduce.py --full --output /tmp/zfc-report-final-replay
~~~

It passed all six jobs: support diagnostics, public table generation,
complete fixed-gap census, complete affine census, exact representative
traces, and one million literal blank moves. Before replay, all 25
entries in the machine provenance manifest matched their hashes.
The recorded machine-readable result is **data/reproduction_result.json**.

The main proof-assistant build was not rerun. Its claims and CI status
remain attributed upstream evidence, with the scope described in the report.

## PDF build and visual QA

Environment: Python 3.12.14; pdfTeX 1.40.25 from TeX Live 2023/Debian.
The manuscript uses Latin Modern and AMS fonts.

Three final pdfLaTeX passes completed successfully. The final log has:

- no undefined citations or references;
- no overfull or underfull boxes;
- no duplicate destinations or other warnings.

All 21 font records are embedded and have Unicode mappings.
The PDF is unencrypted, has no JavaScript, and has letter-size pages.

Every page was rendered and inspected in contact sheets. The theory
statement, normalization, closure/Replacement formulas, gap-census table,
literal counterexample, contents, and reproduction pages were also
inspected at enlarged resolution. The final layout fixes keep the contents
on one page and prevent the artifact-map heading or reproduction command
block from being split awkwardly. A geometric text-span check found no
text outside the page boundaries.

The LaTeX build is reproducible in content and layout; PDF timestamp and
object metadata can change between builds. The manifest identifies the
exact supplied PDF bytes, not every possible rebuild.

## Scope

Finite checks do not establish the infinite EPSC1 schema, an unbounded
binary simulation, nonhalting, or a new calibrated 252-state machine.
The report's ordinary proofs and the exact finite experiments have
different roles and remain explicitly separated.

