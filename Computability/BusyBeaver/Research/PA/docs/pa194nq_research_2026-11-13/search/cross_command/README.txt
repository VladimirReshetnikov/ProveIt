Additional semantic research: cross-command code sharing
=======================================================

This supplement is research material. It is not the requested <=194-state
result. The parent archive's principal 194-state result is separate.

research195/ contains a fully specified 195-state implementation whose new
successful-MP epilogue reuses an already present AX decoder fragment.
Its ordinary consistency calibration is outlined, not claimed as an
independently completed proof. Its physical/source certificates have been
recomputed. The exact proof boundary is stated in SEMANTIC_RESEARCH.txt.

Reproduce the 195-state physical and source checks, without writing files:

    python3 -B research195/reproduce.py

Python 3.10+ and its standard library suffice. Assertions must be enabled.
The frozen successful receipt is research195/reproduction.json.

search/ contains the bounded discovery searches, exact input templates,
attributes, and a ledger of seven completed runs. Their event counts are
not counts of distinct machines and do not prove a state lower bound.
No large logs, executables, rejected tables, or duplicate research packets
are included.

Example optional search reproduction (requires a C++17 compiler):

    c++ -O3 -std=c++17 search/flexible_search.cpp -o /tmp/cross_command_search
    /tmp/cross_command_search search/warm_CSZ_Areturn.txt \
        search/graft_attrs.txt /tmp/cross_command_candidate 180 202611135522

Search termination is based on wall time. A seed and budget reproduce a
search specification, not an identical number of proposals on every host.
The accepted research195 table is reconstructed independently of search.

The copied compiler/runtime and reference Lean sources retain their source
attribution and licenses in research195/licenses/. They were obtained from
ProveIt/Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/
and the repository's jamesyc-upstream/pa196 snapshot. Runtime.lean is retained
as a reference for the inherited arithmetic-block contracts; this supplement
is not a standalone Lean project.
