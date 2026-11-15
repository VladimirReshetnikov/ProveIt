THEORY REVIEW AND A REJECTED SOURCE-DESIGN EXPERIMENT

Positive results in this release are the two separate selector/acceleration
composites. This folder does not claim a further consistency construction.

Reviews
-------
ax11h_dependency_audit.txt reviews the exact revised written AX11H calibration.
composite_review.txt independently reviews the new direct relative theorem.
Both are mathematical reviews with stated scope, not proof-assistant builds.

Reversed Cantor experiment
-------------------------
We tried changing the shared Cantor-pairing arithmetic core by interchanging
registers T and X. The intended source contracts are

  old core: (T=b, X=a, Y=0) -> (T=0, X=0, Y=p(a,b));
  new core: (T=b, X=a, Y=0) -> (T=0, X=0, Y=p(b,a)),

where p(a,b)=(a+b)(a+b+1)/2+b. A shorter Push first moves W to X while leaving
T in place, then calls the reversed core. Therefore the intended stack code
remains p(t,w). The formula constructor becomes I'(a,b)=4p(b,a); the original
four residue tags still distinguish implication, membership, universal
quantification and equality. This is a real source-arithmetic redesign,
not state renaming.

The complete primitive source shrinks from 3,673 to 3,457 sites. However,
our conservative literal lowering has 206 controls. An optimistic raw-action
matching nominates eight folds, giving price 198, already above the target.
The old Cantor reader controls also serve opcode handlers, so several cannot
be removed after the source change. Native controls29 and43 disappear, but
seven new pure-reader controls are allocated. This illustrates the difference
between source-program length and physical working-state count.

The discovery was stopped at this unfavorable price. We did not prove full
physical contracts or validate simultaneous folds for this candidate. The
only executed semantic regressions are 432 finite source cases (three
contracts over a,b=0,...,11). These are not an all-input proof and are not
used in either positive composite theorem. The candidate is explicitly
labeled UNVERIFIED everywhere it is stored.

Replay (Python3 standard library, assertions enabled):

  python3 -B explore_reverse_cantor.py --output /absolute/fresh/directory

The script verifies its attributed input hashes, rebuilds the candidate and
source, repeats the local matching-price calculation, and runs the finite
source regressions. It writes a structured receipt. recorded/ contains the
observed output from this exact script. No repository checkout or network
is needed. PROVENANCE.json and licenses/ preserve input attribution.

An unfavorable price in this fixed lowering is not a lower bound on any
broader family, and a proposed fold count is not a certified quotient.
