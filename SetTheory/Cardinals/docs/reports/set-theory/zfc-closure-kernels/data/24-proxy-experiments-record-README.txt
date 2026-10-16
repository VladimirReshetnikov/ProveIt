ZFC253: finite row census and a complete literal-quotient obstruction
=================================================================

Result
------
The literal 253-working-state binary table zfc_253.tm admits no strict
one-step state quotient preserving writes, head moves, and terminal status.
The certificate distinguishes all 31,878 unordered pairs of working states,
plus all 253 working/terminal pairs. Its words have length at most 12.
The deepest pair is (89,152), with word 101000000000.

This is a finite theorem about one precisely defined transformation class.
It is NOT a lower bound on the number of states required for Con(ZFC), a
minimality theorem for the machine's behavior, or a proof of its consistency
equivalence. An optimization can change tape encoding, alter the program,
use a longer local simulation, or have different initialization behavior.

Exact theorem and elementary proof
---------------------------------
Let Q={0,...,252}, let H=253 be terminal, and let delta be the complete
literal table. Suppose f maps Q union {H} to states of another deterministic
binary table, maps H to a state distinct from every f(q), q in Q, and, for
every delta(q,b)=(w,d,r), preserves the row:

    delta'(f(q),b) = (w,d,f(r)).

Then f is injective on Q. Thus no state quotient satisfying these conditions
has fewer than 253 working states.

For each pair of states the certificate gives a finite binary word.
An empty word distinguishes terminal from nonterminal. A word beginning in
b distinguishes a pair if their b-rows write different symbols or move in
different directions; otherwise its suffix distinguishes their successors.
Induction on word length shows that the two states cannot have the same
image under f. The independent verifier checks every word directly against
the table and verifies exact coverage of every unordered pair.

These words are algebraic distinction obligations for a literal quotient.
They need not be physically realized as successive tape observations in a
blank-tape run. The theorem's row-preservation assumption is the reason
this algebraic distinction is sufficient.

Conditional 252-state runtime quotient
-------------------------------------
When the single row (state0,read0) is omitted from the support, all working
pairs are still distinguished except (0,2). Merging exactly these two states
is a valid quotient of the remaining 505 rows. Consequently this is the
only proper quotient of that partially specified table, up to renaming.
In the old ZFC254 labels it is the identification old5~old64. The omitted
row is used by the literal blank bootstrap, so this conditional result does
not produce a 252-state blank-tape consistency machine.

Finite census, independent of the full-table theorem
--------------------------------------------------
The complete initial diagnostic parsed all 6,460 leaves of the pinned
upstream register program. It ran all 8,391 instruction/branch cases with
concrete register values and explicit finite spare blocks, executing every
literal TM transition, including the register-file operations. All tests
matched their stipulated macro endpoints. Total: 2,849,408 moves; maximum:
484 per case. The finite tests observed 505 rows and all 253 working states;
only row (0,0) was absent. A separate 312,975-step blank run observes row (0,0)
and ends in state 33 with head -17. The union of observed rows is all 506.

The included 187-case witness subcorpus replays all 505 observed macro rows
using 70,968 moves. The default census therefore has no large dependencies.
It also replays the 312,975-step blank prefix. No inference from these finite
tests to all unbounded runtime configurations is made. In particular, the
505-row support theorem above is explicitly conditional. The complete-table
quotient theorem does not use the census or any reachability assumption.

Reproduction (Python3 standard library only)
-------------------------------------------
From this directory:

    python3 make_certificate.py
    python3 verify_certificate.py
    python3 macro_census.py

The independent verifier imports no generator code. It checks the pinned
machine hash, all 506 rows, the source and terminal conventions, every word,
every pair, and the conditional surviving quotient. It does not merely
trust the generator's summary.

Optional full census:

    python3 macro_census.py --program /path/to/Prog254.v --output census_full.json

Prog254.v is data, not executed. The script checks its SHA256 before parsing
the literal tree. Its immutable source URL and hash are in metadata.json.
No script downloads packages, accesses the network, or invokes a compiler.

File guide
----------
zfc_253.tm: exact upstream 253-state table, unchanged.
make_certificate.py: certificate generator using breadth-first propagation.
verify_certificate.py: separate direct word replay and pair-coverage checker.
quotient_certificate.json: complete generated distinction words.
quotient_summary.json: concise machine-generated summary.
macro_census.py: concrete macro/input witness replay; optional full census.
macro_inputs.json: 187 small concrete witness cases and source provenance.
census_replay.json: included-corpus run result.
census_full.json: full 8,391-case run result, needing the optional input to redo.
metadata.json: immutable source and result provenance.

Attribution and status
----------------------
The machine is the 253-state reduction submitted by mira-emmy in
jeff87654/busy-beaver PR 20, head 0d544f2a2e3c18f12278441a74b7879f31cbe856,
derived from Mira-Cult's 254-state machine. The present scripts and finite
quotient certificate are new diagnostics prepared for the ProveIt report;
they do not claim authorship of the machine or its set theory. They use
Andrew James Wade's program/machine conventions, as retained upstream.
The macro path data were extracted from the pinned accepted M254 program.
No Coq library or proof source is bundled here.

As inspected on 2026-10-16, PR 20 was open, and its pinned CI run reported
success rebuilding 160 source modules, auditing 194 closed assumption
reports, and running recursive coqchk. Its endpoint is an external Coq
halting/refutation equivalence. These diagnostics did not independently
rerun that Coq build and do not add an internalized ZFC proof compiler or
a formalized independence result. The report must retain that distinction.
