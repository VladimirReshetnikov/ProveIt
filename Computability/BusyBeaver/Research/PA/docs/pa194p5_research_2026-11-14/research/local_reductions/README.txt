Reproducible finite reduction searches for PA194 and the seven-row register permutation.

Run `node local_search.js` for symbolic context extraction, contextual pair folds,
head-offset deletions and independent incoming-edge bypasses. Add `--extended`
to examine all 334 individually equivalent row rewrites and search for a subsequent
pair fold. Extended search takes several minutes. Node.js 18+; no packages required.

The source checker verification_core.js is retained from ProveIt/Computability/
BusyBeaver/Research/PA/docs/PA194NS_research at commit
4be5c6e3a10292a7466f5d3687e3b39615ff049b. Its four box lemmas remain inherited.
The new local_search.js implements finite local searches and is not a proof assistant.
It excludes the 23 box states as merge targets and uses source/frame context
supersets of radius 6. Local simulations stop after at most 120 transitions and
may not read or write outside their known window. Failure to find a contraction
is not a state lower bound. These are research artifacts, not an end-to-end PA proof.

The receipts were produced in V8 during this session. The local Node entry point
reproduces the same functions. data.json contains both native tables, the 3,673
source sites and the instruction graph. No private data is included.

