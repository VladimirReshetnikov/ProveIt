Decoder255 offline reproduction bundle
======================================

From the archive root (Python 3.10 or later, standard library only):

  python code/reproduce_decoder255.py --output /tmp/decoder255-replay

The script checks all pinned input hashes, makes the four upstream PR20
initializer changes, deletes state 8, checks 8,391 affine instruction cases
with the original 55 protected register-box rows, and runs exactly 606,702
blank-tape steps to an admissible gap-41 frame. It also simulates and matches
the first 676 register-machine steps. It writes both original-label and
normalized tables, the state map, and a complete JSON endpoint certificate
into the output directory. The normalized table must have SHA-256:

  f4aad63fe10699100aa48a0da22bb4582f76d641e9f8a0c3d9123055d066b29f

The normalized table has 255 working states, 510 rows, start state 0,
terminal state 255, and a blank 0 tape. All working states are graph reachable.
The old-label simulation uses start 5, dispatcher 96, and halt 254; these are
labels, not a second machine-size convention. The state map relates them.
The earlier exact initial register frame has gap 37 and cannot justify the
source09 gap-41 affine certificate; the later proved source-program suffix
is essential to the experiment.

Optional bounded search (about half a minute in the research environment):

  python code/reproduce_decoder255_folds.py /tmp/decoder255-replay

It checks 57,150 directed one-state substitutions within the specified
protected-state and 500-affine-step limits. No substitution survived. This
negative result establishes no lower bound or minimality theorem.

STATUS: executable engineering experiment, not a new Coq/Rocq certificate,
not a smallest-known result (upstream PR20 has a different 253-state machine),
and not an internally arithmetized ZFC proof. The affine audit uses the
upstream register-box contracts as an oracle after checking that their 55
protected transition rows are unchanged. No claim is made that this Python
audit proves those contracts or imports their Coq proofs into Python.

PROVENANCE.json pins the input files and repository revisions. The original
ProveIt and Cardinals repository MIT-0 notices are also preserved.
SOURCE09_README describes the larger original package, whose optional inputs
are not all included here; run the outer reproducer shown above. Original
source09 documentation is preserved as SOURCE09_README.md. LICENSE.wade is
the license supplied for Andrew Wade's framework; its scope is not extended
to source09 or Jeff's other artifacts. No additional licensing is asserted.

formal/FullZFC253.v elsewhere in this archive is UNCOMPILED proposal source.
It composes existing upstream external finite-refutation equivalences; its
comments explicitly distinguish that from the required internal ZFC theorem.
