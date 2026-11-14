COMPARISON AND TRANSPLANT RESEARCH BUNDLE

This bundle does not contain a certified machine with fewer than 196 working
states. Read the status of each experiment before using a transition table.

1. comparison/compare_designs.py rechecks 30 pinned presentations, including
27 incoming U208 presentations in 20 exact rooted transition-graph classes.
It also checks the source CFG,18 local helper equivalences, and the complete
published PA196/PA209 finite startups.

  python comparison/compare_designs.py --output comparison_replayed.json

current_bindings_receipt.json rebinds the 30 inputs to ProveIt commit
 dc523e7b06ffb414093c90aa035500ca283e5f75
and BusyBeaver commits407cdc356f6b586635e71ac92be394255f4bfea4 (PA196) and
69d98241a721ead20b4f0b17df9062950b40fbfe (PA209).
The comparison's older metadata still names the earlier ProveIt commit; the
fresh receipt proves byte identity to the present pinned archive files.
All 18 incoming ZIPs are inventoried. Archives themselves are not bundled.
To rebind them again, check out these commits, then pass their paths:

  python check_current_bindings.py --incoming PROVEIT/docs/incoming \
    --comparison comparison --busybeaver PA196_CHECKOUT \
    --busybeaver209 PA209_CHECKOUT --output rebound.json

accepted196/ contains 9 published or incoming accepted 196-state layouts.
Their hashes and distinct rooted classes are recorded in its manifest.

2. scanner196/ is a newly verified 196-state layout with the same exact source
CFG as published PA196. It passes 4959 symbolic arbitrary-value contracts and
the exact candidate2 blank startup at 58294 steps. Its 15 internal six-zero
address obstructions improve the studied scanner layout but do not yield a
shortened scanner: no 195-state machine is claimed.

  python scanner196/verify.py scanner196 --startup 150000

3. hybrid/ combines the U208 outer source skeleton with PA196 AX. The source
has 3810 primitives, 159 distinct internal subtrees, and 147 physical readers.
The complete 196-state table passes 4957 arbitrary-value full-tape contracts,
covering all 392 rows, with arbitrary gap, nine registers and finite spares.
Its blank-tape behavior is WRONG for the desired consistency machine: each
of its 196 possible initial controls reaches an explicit outward self-loop.
These are finite checked counterexamples to using this interpreter as a
blank-start construction. It is an interpreter experiment only.

  python hybrid/transplant.py hybrid/pa196.native.tm hybrid/p196.sites.json rebuilt
  python hybrid/contracts.py hybrid/hybrid196.native.tm \
    hybrid/hybrid.sites.json hybrid_replayed.json
  python hybrid/screen_initial.py hybrid/hybrid196.native.tm \
    hybrid/hybrid.sites.json hybrid_initial_replayed.json --bound 150000

The diagonal/ and separate/ hybrids also have 196 states and the same failed
all-control blank-start result; their whole-runtime contracts were not rerun.
bootstrap197/ repairs the bootstrap address prefix and reaches an exact
canonical frame at 47068 steps, but introduces seven-zero source addresses;
its zero case at source site 842 fails the full runtime check. It is rejected.

All executable contract checks are mathematical checking code outside a
proof-assistant kernel. Source equivalence and finite startup must be combined
with the separate arithmetic/proof-enumeration theorem; these files do not
assert that bounded simulation proves nonhalting.
