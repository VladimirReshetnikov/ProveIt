PORTABLE AX ASSOCIATION SEARCH

The three recorded runs each used a 240-second wall-clock budget. Their attempt
counts were 91,792 (original, zero bound6), 99,064 (original, bound5), and 92,720
(diagonal, bound6). These counts include duplicates and sampled nodes without
an admissible rotation. They are observations of the original runs, not counts
of distinct tested machines or an exhaustive set of grammars.

From this directory, reproduce the three search procedures with:

  python3 ax_association_search.py --seconds 240 --seed 601 --zero 6 --out rerun_original_zero6
  python3 ax_association_search.py --seconds 240 --seed 313 --zero 5 --out rerun_original_zero5
  python3 ax_association_search.py --seconds 240 --seed 793 --zero 6 --initial diagonal191.grammar.json --out rerun_diagonal_zero6

These commands require only Python3's standard library. Rerun counts and the
best result reached before timeout depend on machine speed, concurrent load,
and Python version. A fixed seed does not remove wall-clock cutoff variability.

To check the saved witnesses without restarting any search:

  python3 verify_saved.py

That check recomputes the scoring tuple of each recorded best grammar and checks
its source word and zero-run/entry constraints. It does not authenticate the
historical number of search attempts independently of the retained log. The
receipts and logs record that history.

The score subtracts a maximum matching of potential context folds. It is a
screening score, not a proof that all selected folds can coexist. The delivered
198-state diagonal witness was separately reconstructed and verified against
every source primitive branch in the main diagonal198 directory. The bound5
winner is only a search witness, not a valid lower bound or a 207-state claim.

The source inputs are pinned PA196 at revision407cdc356f6b586635e71ac92be394255f4bfea4
and the supplied diagonal191 AX grammar. The original stochastic driver was
ported by replacing its absolute imports with the included dependency subset.
No new search was run while preparing this portable reproduction package.
