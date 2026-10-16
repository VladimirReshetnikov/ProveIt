EPSC271 offline inputs and attribution
=====================================

TMBuilder.py, tm.py, and tmdb.py are unchanged Andrew James Wade backend
sources retained by ProveIt from jeff87654/busy-beaver commit
297ab8df7e5de329605c3875b4934643b371a5e3. LICENSE.wade is the original
MIT No Attribution license. No remote retrieval is needed to regenerate
the table in this package.

epsc270_dag.json and full_equality_epsc.py come from the user-provided
zfc_empty_seed_research.zip, found in ProveIt/docs/incoming at the inspected
commit af518abcf8ca2a7c1b795c07973885041aee0d25. The first is the earlier
270-state EPSC compiler control's exact register DAG. The second is its
literal schema source; the offline low-code audit calls only empty_psc.
The original incoming source acknowledgments are INCOMING_NOTICES.txt.
The earlier grammar optimization is credited to that incoming report.

theory_syntax.py supplies only the pure symbolic constructors used by the
retained EPSC function. It is compatible with ProveIt's corresponding
definitions; it performs no repository lookup or network operation.

code/reproduce_epsc271.py adapts the small builder adapter and structured
register-helper interpreter from ProveIt's recover_wade_dag.py and
pairing_backend_experiment.py. Their MIT-0 repository license is retained
as LICENSE.ProveIt. The new transformation shifts the membership family
from4P+1 to4P+5 by adding one register-DAG node; it reserves code1 for a
genuine closed Bottom. The complete original logical interface is retained.

The new source-level low-code theorem is in sections/low_code_epsc.tex.
The finite checks and table generation do not provide the remaining
universal literal-machine/initializer simulation or a new state bound.

From the package root:
  python code/reproduce_epsc271.py --output /tmp/epsc271-reproduction
  python code/check_low_codes.py

Exact source and output hashes are in data/epsc271_provenance.json and
data/epsc271_results.json. The normalized table has271 working states,
one halt label271, and542 transition rows. Its sole previously undefined
backend row is completed by a transition to halt; the partial and total
halting conventions therefore agree. This completion is not a proof of
the program-to-machine interpretation.
