SUPPORTING N6 SOURCE SEARCH

Conservative zero/positivity analyses and 936 combinations of three return-row edits.
No bisimulation or tested one-bit fold was found. These finite searches do not
exclude different source programs or a different physical register allocation.

All input tables, source trees, grammars and inherited runtime scripts are
bundled. Python standard library only, assertions enabled. From this directory:
  python3 analyze_zero.py
  python3 jump_options.py
  python3 combine_jumps.py

The jump_options worklist keeps explicit (source PC, nine-bit positivity mask)
pairs. The completed run reported 271404 distinct pairs at 3776 source sites.
The earlier analyze_zero.py is a separate pointwise-join overapproximation.
The symbolic interpreter inherits arithmetic-box lemmas; no new proof-assistant
endpoint is supplied. See ../../licenses/ for upstream notices.
