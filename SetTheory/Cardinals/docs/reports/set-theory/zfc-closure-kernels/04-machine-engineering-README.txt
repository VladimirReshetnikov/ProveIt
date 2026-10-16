MACHINE-ENGINEERING AUDITS
==========================

These scripts and their JSON outputs accompany the research report. They
separate exact finite table calculations from symbolic diagnostic searches.
Python 3.10 or later and only the Python standard library are required.

The upstream machine tables, decoder program, and symbolic executor are not
redistributed in this directory. sources_manifest.json identifies four
immutable public inputs by commit, byte length, and SHA256. Fetch them:

  python fetch_sources.py --output sources

To verify an already downloaded set without any network access:

  python fetch_sources.py --output sources --verify-only

All following commands assume the current directory is this directory.
They create JSON reports locally and make no network requests:

  python analyze_table.py sources/zfc_254.tm sources/zfc_253.tm --output structural_results.json
  python grammar_audit.py sources/Prog254.v --output grammar_results.json
  python context_search.py --sources sources --search --all-noncore --output redirection_results.json
  python runtime252_audit.py --sources sources --output runtime252_results.json
  python blank_start_certificate.py --sources sources --output blank_start_certificate.json
  python bootstrap_search.py --sources sources --fuel 2000000 --output bootstrap_results.json

No formal verification compiler is downloaded, installed, or invoked.

WHAT THE CALCULATIONS ESTABLISH
------------------------------

1. Structural table audit.
   The 254-state and 253-state literal tables have every working state
   reachable in the abstract control graph. Neither contains duplicate
   transition rows. Deterministic partition refinement, preserving the
   written symbol and head direction for either input symbol, identifies
   no pair of different working states. This is an exact finite result
   about that restricted quotient notion. It is not a lower bound on any
   equivalent Turing machine, and control-graph reachability is not
   blank-tape semantic reachability.

2. Decoder grammar audit.
   The pinned program contains 6,459 internal tree nodes and 6,460 leaves.
   Hash-consing identical ordered subtrees leaves 203 internal nodes and
   23 leaf labels. The maximum leaf depth is 34. The script also measures
   340 single adjacent swaps of different-register increments and all
   eight whole-class swaps for the three observed pair types. None improves
   the baseline sharing count. These are syntax costs, not binary-machine
   state counts; the perturbed programs have not been certified equivalent.
   In particular, an outside control edge entering a pair's interior can
   invalidate a naive commutation argument.

3. Diagnostic state-redirection search.
   The pinned published affine executor accepts all 8,391 instruction cases
   (6,460 leaves, with the 1,931 decrement leaves checked in both branches)
   for the 253-state table, at invariant gap 40. The search tries deletion
   and direct retargeting of each of 223 observed noncore states to each
   of the other 252 states: 56,196 candidates. None was accepted. Register
   box states and dispatcher 96 are protected. A run failing the symbolic
   checker, or exceeding its fuel limit, is not a proof of inequivalence.
   The search does not cover coordinated multirow edits, altered programs,
   stronger reachable-state invariants, or different tape encodings.

4. A 252-state runtime body, with the blank initializer still missing.
   In the 253 machine's old labels, state 5 on symbol 1 and state 64 on
   symbol 1 have the same transition, 1 R 64. Deleting old 5 and redirecting
   old 49/1 to 64 preserves every one of the 8,391 symbolic runtime cases.
   The resulting body has 252 states and 504 transitions, but the removed
   state's symbol-0 transition is its blank initializer. This is not a
   complete 252-state solution. All noncore transitions are read somewhere
   by the current macro-level overapproximation, so it offers no immediate
   unused startup branch.

5. Exact classification of every blank start for that body.
   The separate blank_start_certificate.py computes at most 44 literal
   moves from each of the 252 possible start states. Exactly 234 choices
   enter a self-loop moving into an all-blank ray. Such a configuration
   runs forever by induction, even if the self-loop writes 1 behind it.
   The other 18 choices reach, up to translation, exactly this common
   configuration: old state 96, head 0, tape 1 exactly at positions -1
   and 3. No other cells contain 1. Those 18 old labels are
   0,28,31,38,40,43,44,56,59,60,64,69,73,75,83,85,97,112.

   Thus changing only the start state leaves one unresolved execution
   orbit after the trivial nonhalting choices have been removed. The
   common configuration's halting behavior is not determined here. Its
   two 1s do not encode the required initialized register file or gap-40
   runtime invariant. This classification is an exact finite certificate
   combined with the elementary blank-ray lemma, not a bounded simulation
   inference about nonhalting. A kernel-checked port is not supplied.

6. Longer blank-start diagnostics for that body.
   Every one of its 252 choices of initial state reduces exactly, before
   the first written 1, to a zero-writing cycle or one of seven first-write
   representatives: old 0, 7, 20, 42, 83, 95, 112. The scripts then run each
   representative for at most 2,000,000 literal moves. None reaches the
   tested gap-at-least-40 dispatcher frame. These finite trials do not
   prove that all starts fail forever, nor do they show that an arbitrary
   matching frame would have the required register-program history.

TRUST AND PROVENANCE
--------------------

context_search.py and runtime252_audit.py deliberately execute a SHA256-
pinned portion of the published symexec.py design model. They use its four
register-box summaries, preserving the transitions used by those summaries.
The fresh JSON reports are diagnostic computations, not Coq or Lean kernel
certificates. The upstream 253-state formal proof and its CI evidence are
discussed separately in the main report.

The 254-state machine was designed by Mira-Cult. The pinned m254 Coq
verification and its design-model executor are from jeff87654/busy-beaver.
The 253-state reduction is from mira-emmy/busy-beaver, branch
zf253-exact-equivalence, commit
0d544f2a2e3c18f12278441a74b7879f31cbe856, submitted as upstream PR 20.
Source locations, immutable pins, and authorship notes are in the manifest.
No original authorship of either record machine is claimed here.
