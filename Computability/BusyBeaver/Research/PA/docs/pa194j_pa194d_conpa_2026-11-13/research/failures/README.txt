Rejected reductions
====================

scanner_fails.json lists the 113 failing universal cases after removing
scanner control 34 and redirecting it to 75 in the supplied primary PA194 table.
The original source has 3,673 sites and 4,780 outcomes. Each record gives
the source ordinal and the physical unary register's zero/positive case,
or null for an unconditional case. This exploratory check used the primary
symbolic engine. It is negative evidence, not an accepted 193-state machine.
In particular source site 25 fails, so AX-only address changes cannot make
the patch valid without further work on the fixed source paths.

zero_spare_bootstrap.py reconstructs the separate, rejected zero-spare
patch on the frozen PA194CS parent and reproduces its finite drift witness.
It leaves the delivered machines unchanged. Once state 35 is to the right
of every one-cell, its literal 0-row writes 1, moves right, and stays in 35.
Induction proves permanent drift because every next scanned cell is a fresh 0.
This is an explicit bootstrap failure, not merely a timeout.

No rejected table is labeled as a PA consistency construction.
