Independent physical audit of even195HX
=====================================

This directory contains a portable independent checker and frozen inputs
for the 195-state stride-two research construction. It is separate from
the main PA194H5 fallback construction.

Run, using Python 3.10+ and its standard library, without -O:

    python3 check.py
    python3 check_source_delta.py

The default inputs/ directory contains the exact literal native and dense
transition tables, state-label map, source sites, resolved instructions and
the construction's source bridge. The checker does not import or execute
the construction compiler, does not read verification.json as an oracle,
and does not assume arithmetic-box correctness.

It independently checks:

* All 390 binary transition rows for 195 working states, graph reachability
  from native start 74, one external halt 254, and dense/native conjugacy.
* The complete source graph twice, using arithmetic and interval resolvers;
  agreement with the delivered 3,674 resolved source instructions.
* Four register-list traversal lemmas directly from the literal rows.
* Every one of the 4,781 branch-sensitive source outcomes for arbitrary
  natural primary registers, an arbitrary affine header gap, and any
  nonempty finite list of natural spare-register values.
* The register permutation PHY=(6,2,0,4,3,8,7,5,1), including the new
  native control 3000.
* Complete blank initialization after 44,094 literal transitions, reaching
  native state 84, head -2, source site 40, logical registers
  (4,0,0,0,0,0,0,0,1), gap 0, and 29 spare values equal to one.
* The entire finite-support tape and zero exterior at that boundary.
* An independently executed 48-source-step bridge to site 25 with logical
  registers (4,0,0,0,0,0,0,0,0), the clean candidate-four boundary.
* Exact comparison with the frozen primary source: one new inc0 at site 31,
  with all 3,673 old sites preserved and all but one edge exactly relocated.
  The sole redirected edge enters the extra increment from the fresh-candidate
  branch. The restoration loop skips it, so the increment occurs once.

Certificates are written to recorded/: all physical contracts, four list
lemmas, the blank tape, the full bridge, resolved source instructions and
the summary receipt. The physical durations are checked positive, so the
source bridge composes with the universally verified physical contracts.

The executable universal certificates are ordinary mathematical evidence,
not a newly compiled proof-assistant theorem. Completeness of the stride-two
enumeration and the inherited logical PA calibration are separate arguments
in the enclosing research report. A 195-state construction does not improve
the requested 194-state bound.

The reused symbolic engines and their copyright/license notices are under
reference/. Exact frozen-input and engine hashes are in PROVENANCE.json.
