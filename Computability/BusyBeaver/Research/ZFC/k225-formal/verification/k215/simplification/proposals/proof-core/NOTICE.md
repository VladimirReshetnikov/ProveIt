# Attribution and provenance

This research packet is based on Vladimir Reshetnikov's ProveIt repository,
commit aa66d0a33f1f8237a348899eb8095b045a502832. New code and report source
are supplied under the repository's MIT No Attribution license, included
as LICENSE. Third-party components retain their own notices and licenses.

The implication proof keeps the pinned Source149/CD230 ancestry and lemma
labels. New contributions are the thirteen schematic MP substitutions,
dependency pruning, arbitrary-carrier proof, direct final implication
argument, four-scheme specialization, exact CFour adapter, and checked
ports/integration. Search and generators are untrusted proof producers.

The normalized source certificate, path codec and minimal Rocq source
dependencies derive from K215_Checked_Simplifications_2026-10-21.zip.
Balanced lookup derives from K215_Certificate_Refinements_2026-10-21.zip.
Their notices are in provenance/ and source_checker/licenses/ contains
all inherited license texts for the minimal dependency copy. The new
BalancedNormalized and Source215BalancedNormalized files compose those
refinements; neither preceding refinement is claimed as new.

The optional PositiveSimulation theorem is inherited from an earlier
FM215 proof-compression proposal; the KSim numerical-runtime adapter and
checked production-interface integration are new. Detailed provenance is
retained in proofs/README.md and its source records.

Machine input tables and any vendored checking utilities retain upstream
notices in machine_research/. The search scopes and tool-generated
certificates are documented separately from proof-kernel results.
The new hidden-coordinate model covers a logical fragment, not the full
set-theoretic axiom bundles.

Incoming archive hashes and the exact baseline are in provenance/.
Source-to-check receipts preserve the original tool run paths for audit;
portable replay scripts do not depend on those historical paths.
