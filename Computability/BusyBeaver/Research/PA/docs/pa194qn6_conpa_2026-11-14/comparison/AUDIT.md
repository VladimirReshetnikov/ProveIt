Recognition and comparison audit
===============================

1. Exhaustive file inventory, explicitly delimited machine recognition

Every tracked blob in PA and docs/incoming at revision
2337ce611a26e308697ccbddb2a1636f989f01c3 is listed in tracked_files.tsv.
All 66 delivery packets were compared at the level of their recorded
contributions and README/proof/search evidence. This is stronger than looking
only at principal filenames, but does not claim that every historical proof
and every unsuccessful search run was independently reconstructed.

The recognizer accepts complete numeric five-column binary transition tables
in .tm/.txt/.tsv/.csv, complete textual tables nested in JSON values, and complete
five-column row arrays nested in JSON. It recursively visits ZIP members and
nested ZIPs without extracting untrusted path names. The supplementary scan
resolves every reported large-JSON exclusion in the pinned corpus. Thus there
are no unresolved size/depth exclusions for these formats in this revision.

The census does not execute arbitrary generators or infer machines from Lean,
Python, C++, alternative dictionary encodings, PDFs, diagrams, prose, or partial
row sets. Such descriptions remain part of the packet comparison, but are not
literal graph occurrences. "All designs" here therefore means every identified
delivery and literal design in the explicitly delimited source corpus, with
these recognition limits made visible.

2. State counts and equivalence

Working states are distinct source labels with exactly two binary transition
rows. Rowless destinations are recorded as halting labels and are not counted
as working states. Fixtures with no halt, several halt labels, or disconnected
padding are retained in the raw census and excluded where a full one-halt graph
is required. Multiple rowless halt labels are identified by the broad census
hash convention, which is another reason to use its one-halt subcount for the
headline comparison.

The broad table_class matches the repository's maximal-component convention:
for each possible root, enumerate the reachable directed graph in binary row
order; retain roots with maximal reachability; select the minimum digest. This
is a full graph invariant only when a graph-spanning root exists. Disconnected
components outside the chosen maximal component are not represented by that
digest. Consequently 576 buckets must not be called 576 complete TM isomorphism
classes without the qualification. The 563 full one-halt buckets avoid these
particular ambiguities. No theorem is inferred from a hash match.

The frontier novelty checker is stronger and uses exact tuple equality for
its decision. It canonicalizes all roots, reflection and symbol complement,
and erases terminal-edge write/move. All 76 existing full 194-state graphs are
still pairwise distinct under this enlarged equivalence. A candidate unequal
to every tuple cannot be a simple relabeling, changed start, mirror, bit-swap,
or final-halt-action variant of one of those literal graphs. The broader
equivalence is conservative for novelty: symbol complementation alone does
not preserve the zero-blank initialization convention.

Dense label zero is inferred as a convenience when no start is declared.
Some historical comparison exports relabel states without carrying the real
start. Such inferred rooted hashes do not certify initialization. Structural
novelty deliberately considers every spanning root. Blank startup correctness
is a separate machine-specific obligation.

3. Historical duplicates and differences

The supplied names do not give a count of distinct constructions. PA194C
reappears in several packets; QN and NQ have the same literal graph; QNS is
repeated; N6 is repeated. Conversely the name NS labels both a cache-only-guard
machine and a different symmetric comparison with the sum guard in different
packets. The primary 67-reader/seven-fold construction differs from its
68-reader/eight-fold alternate. The frontier ledger resolves these using table
identity and source evidence, rather than names alone.

4. Evidence boundary

The census freshly recomputes syntax, counts, row graphs, archive provenance,
and finite structural novelty. The named evidence categories and 196-class
mapping attribute prior supplied manuscripts, proof transformations and runtime
receipts. They do not claim fresh physical or logical certification of every
historical candidate.

The accepted ordinary mathematical arguments for the 194/195 family concern
PA-provability of the halting/refutation equivalence. The repository separately
records unfinished machine-specific iPRA/Lean goals. An unfinished formal
endpoint is not itself a refutation of the ordinary PA argument, and an ordinary
argument is not a completed kernel-checked endpoint. Both distinctions matter.

The rejected coefficient-three machine is blocked by an explicit formula-code
collision and supplied refutation; the later all-offset obstruction is limited
to that fixed interface. The runtime193 contraction preserves source steps but
has no verified compatible blank startup. Neither is a valid blank-start
193-state Con(PA) machine, and neither establishes a general 194-state lower
bound. Restricted selector/fold bounds and finite mutation searches likewise
apply only to their expressly stated search classes.
