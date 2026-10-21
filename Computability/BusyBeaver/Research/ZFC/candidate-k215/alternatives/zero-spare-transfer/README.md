# Zero-spare transfer215 and further alternatives

## Result

A calibrated 215-working-state candidate combines the established three-command
transfer-pop source with the published append-zero spare policy and a newly
proved protected blank startup. It is not a new calculus or a 214-state result.
The 214-state target remains open. Two further checked 215-state layouts are
included. A different no-successful-MP-zero-push language has a complete compiler
but currently requires 216 states.

Read report.pdf (12 pages) first. Its source is report.tex. The inherited
numerical-calculus/ZFC bridge, arithmetic contracts, new compiler arguments,
protected-credit inductions and executable whole-tape evidence are carefully
separated. This is ordinary mathematical calibration, not a new Lean/Rocq
endpoint for these exact bytes.

## Primary machine

primary/machine/zero_spare_transfer215.tm is the start-0 canonical table:
215 working states 0..214, separate halt 215, binary symbols, two-way tape.
Its SHA-256 is
60eae1c30d214f71c65a207087dc716ba4cdad2a1a62c51e9e107434a0ceb4f1.
The native table has start74, separate halt254, and SHA-256
29a6ed4a594d7f974cf267a9e6b665af34c9afd8dd7abbbecf0b538ecab151e0.

The source has201 DAG nodes, not201 TM states. Its4,775 primitive occurrences
yield6,209 arbitrary-natural cases. The complete append-zero runtime uses
1,611,489 symbolic rules and all430 rows. Exact blank startup takes73,172
steps; the177-primitive AX bridge leads to eight safe heads above opaque
unsafe tail171. Scheduler debt3 leaves permanent margin5. Do not regard the
unsafe GEN output18 as a theorem, or confuse logical protected heads with
physical spare-register blocks.

## Structure

- primary/: new calibrated zero-spare transfer215 and full owned replay.
- secondary_association/: alternative S-body association, also215 states.
- optional_reparse/: alternative source reparse, also215 states.
- mp0_216/: complete no-push compiler and calibrated216-state realization.
- supplement/: exact mathematical results, pinned graph comparisons,
  constructor correction and bounded state35 check. Rejected tables live in
  negative_controls; comparison inputs are inert data, not promoted machines.
- report.pdf/report.tex: useful results first, proofs and exact remaining scope.

## Reproduce

Use Python3 with assertions enabled, standard library only. No network,
external checkout, received program, install, proof search or large scratch
file is required. The work directory must not already exist.

    python3 -I -B verify_all.py --work /absolute/path/to/new-output

This checks the full release manifest and all finite component checks, the
prefix certificate, exact source-translation correction and all171 pinned
graph comparisons. To rederive every included machine's universal runtime:

    python3 -I -B verify_all.py --runtime --work /absolute/path/to/new-full-output

Use --jobs 4 to run independent components concurrently.
Each full runtime takes roughly2 minutes on the preparation machine; actual
speed varies. Each component can also be replayed separately; see its README.
To add the old-policy all-natural state35 separator and bounded synthesis:

    python3 -I -B verify_all.py --runtime --state35 --synthesis --work /absolute/path/to/new-complete-output

Only --synthesis requires an installed C++17 compiler (c++ or g++). No binary
executable is shipped. Main machine replay does not need a C++ compiler.
Never use Python -O or PYTHONOPTIMIZE, which disables assertions. Helper
modules are libraries; use the documented verify entrypoints.

## Evidence limits

Fresh isolated full replays are recorded in each component, with exact census
hashes and source/table identities. Written all-natural arguments are not
replaced by finite500,000-candidate checks. The93-member upstream table audit
and broader source-pricing searches are archived scope-specific evidence,
not regenerated downloads/searches in this compact runner. The modal-B
countermodel refutes theorem-set equality; refutation equivalence remains open.
No local-search failure is a state lower bound.

## Attribution and preservation

The append-zero policy is from ProveIt commit
cd596116875419a0cc1b0665cc1c58c7b9f5a135. The transfer language is the prior
contribution included at7342ae8c96c325bb8340291f43d7573866a77cd7.
This packet contributes their composition and new startup proof plus the
stated alternative-language/algebraic results and owned checks. The report
provides direct pinned links. Licenses and inherited attribution are retained
inside primary/ and mp0_216/. Historical paths in proof/provenance documents
are archival references, not runtime dependencies. All executable checks are
owned; received source/table/certificate JSON is inert data.

The two earlier delivered ZIP archives were not modified or republished as
this result. MANIFEST.json authenticates all other shipped files; its own
hash and the archive hash are recorded outside the archive in the release
receipt, avoiding self-reference.
