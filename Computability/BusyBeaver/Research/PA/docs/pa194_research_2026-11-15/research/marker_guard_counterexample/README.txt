REJECTED 193-state marker/guard repair

The familiar runtime 301->88 fold is combined with 122/0:0L174 and 174/0:0R30.
This is a recheck of a previously proposed repair, not a successful construction.
All 4,780 primary-source outcome contracts were tested, instead of stopping at
the first failure. There are 88 failed outcomes, at source sites 3554--3620
(the GEN subroutine). The blank execution reaches an outward state 35 ray at
time 92. The complete recorded failures and finite trace are retained.

Optional replay: run check.py from a disposable output directory. It reads
../physical_searches/primary by a path relative to its own file; no network
is used. It writes guardpatch193.native.tm in the current directory.
The inherited symbolic executor and its arithmetic-box assumptions are
documented in ../physical_searches/README.txt and retain their licenses.
