SCOPED REDUCTION SEARCH, 15 November 2026

This folder preserves the additional reduction attempts made from the pinned
PA194LCG parent and the new PA194LCGMS composition. These are negative results
for stated finite screening domains. They do not rule out 193 states generally.

Reproduce the finite source closures and all five optimization screens:

  python3 reproduce.py

Also regenerate all symbolic context envelopes (several minutes):

  python3 reproduce.py --regenerate

Requirements: Python 3.10+ standard library and a C++17 compiler named g++.
Use --compiler to select another compiler, --output to select a fresh output
directory. No network, proof assistant, or nonstandard Python module is used.
Do not invoke Python with -O: assertions implement certificate checks.

DEPENDENCIES AND CHANGES

input/machine.native.tm, sites.json, instructions.json and parent_k6.tsv are
the pinned PA194LCG inputs from pa194_loop_return_2026-11-14. The source table
is independently reconstructed by the arithmetic and interval resolvers in
reference/source_language.py before an abstract closure is computed.

The reference/ files originate in that supplied research archive. The only
change to its symbolic_runtime.py adds an optional values_override to case(),
so symbolic register inputs can satisfy independently established invariants;
its literal step interpreter and whole-list lemmas are unchanged. The supplied
licenses are retained. collect_parent_contexts.py is copied without changes.
collect_guarded_contexts.py extends it with marginal register constraints.

cpp/closure_marginals.cpp adapts the earlier PA research closure.cpp. It tracks
the nine registers JOINTLY, at every source site, using either {0,1,>=2} or
{0,1,2,>=3}. At the largest abstract value, decrement has both the immediately
lower and the largest abstract successor. Every reached abstract edge is
checked again for closure. Only then are marginal bounds projected for use in
the symbolic frame interpreter. Exact small values stay exact; any more complex
union is safely weakened to its minimum plus an arbitrary natural parameter.
The actual incoming source state is therefore covered by a symbolic case.

The two C++ physical optimizers are the pinned loop-return research programs.
They accept explicit radius-six envelopes. Their domains are: all 18,721
unordered pairs of the 194 controls, all common row actions, old continuations
of at most 24 steps and new continuations of at most 256 steps; and independent
incoming-row bypasses for each of the 193 noninitial controls, old continuations
of at most 48 steps and new continuations of at most 512 steps. Paths must stay
within the available six-cell window in each direction. These restrictions
make the search finite and explain why no-hit results are not lower bounds.

The physical window envelopes cover the symbolic source-frame traces, the
interiors of accelerated unary and arbitrary finite-list operations, and the
complete blank startup. For the new MS machine, transfer.py includes every
intermediate configuration of the exact local marker-separation simulation;
unknown new boundary bits are included both ways. No observed blank prefix is
extrapolated to an all-time invariant.

recorded/ contains immutable envelopes, closure data, and optimizer logs from
this session. manifest.json checks these inputs before reproduction. Generated
receipts record executable facts, not Lean kernel theorems. The mathematical
scope and final counts are in ../search_results.tex.
