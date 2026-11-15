# Safe-premise-exchange grammar search

This finite heuristic experiment exchanges the implicational premises of at least one of ordinary congruence heads 3 and 4, optionally also exchanging distribution head 6 and varying the diagonal/parameter pattern. Three associations for each of 12 combinations give 36 seeds, recorded in `seed_meta.json`. The proof-preserving translation is in the archive root's `proof/exchange_and_brouwer.tex`; it uses exchange derived from the retained dominated propositional basis alone.

The exact fixed core and source trees are embedded in `templates.txt`; `leaf_attrs.txt` supplies matching macro attributes. The C++ search and screen derive from the incoming GD research. The adaptive elite pool keeps candidates within 2 points of the current best instead of a fixed threshold, so an initially higher score does not discard every useful intermediate mutation.

From this directory:

```sh
g++ -O1 -std=c++17 search_adaptive.cpp -o /tmp/pa194_exchange_search
/tmp/pa194_exchange_search templates.txt leaf_attrs.txt replay 420 20261114002 > replay.log
```

The recorded 420.002-second run proposed 2,620,420 iterations and accepted 272,848 mutations. Best reader score improved from 67 to 62, with zero penalty; there were no hits at score ≤ 60. The CSV is therefore correctly header-only. With the fixed 134-control core the best screen score corresponds to an optimistic 196-control construction.

Moves reassociate binary source trees and independently permute freely instantiated head parameters. Fold opportunities are limited to those modeled by the screen. Any hit would still require complete construction, source binding, physical contracts and blank startup. The saved best grammar is not a certified machine. The seeded trajectory is deterministic until a hardware-dependent wall-time cutoff; this negative result is not an optimality theorem.

All 36 seed grammars, best grammar, complete log and numeric templates are supplied. No repository checkout or network access is needed. The archive manifest binds all files. Upstream attribution and licenses are in the archive root and grammar-search bundle.
