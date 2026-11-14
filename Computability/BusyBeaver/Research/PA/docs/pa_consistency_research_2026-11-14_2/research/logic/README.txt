LOGICAL-HEAD EXPERIMENTS
========================

Outcome
-------
Neither experiment produced a verified machine below 194 states. The first
experiment is deliberately retained as a failed logical lead. Replacing the
old first head O=(exists_d U(d,H))->H by positive Brouwer alone loses the
established explosion interface; the main report gives an exact countermodel.

The repaired presentation retains Brouwer and adds an explicit head 1->C.
These two heads are uniformly interderivable with O over the common rules.
This is a source-level mathematical fact. The resulting eleven-head emitter
still needs changed selectors, an all-store compiler and physical validation.

Recorded bounded runs
---------------------
Domain                    Templates  Tokens  Proposals  Accepted  Best score
Brouwer-only diagnostic          32     190    5798229   1714703          63
Brouwer plus explosion          288     194    4904863   1511235          65

Seeds are 2026111331 and 2026111332; budgets are 360 and 300 seconds. No run
reported a threshold hit. The corrected best score plus the 134-control core
is an objective of 199, not a verified 199-state table. These are stochastic
grammar screens with scanner constraints and nominal pairwise fold matching.
They do not prove minimality of the source or of the machine class.

Reproduction
------------
The upstream/ directory contains all input files needed for preparation.
From this directory:

  python3 -B make_brouwer.py
  python3 -B make_brouwer_explosion.py

The saved preparation and best macro words can be checked without searching:

  python3 -B verify_saved.py

These commands regenerate the frozen template inputs, variant descriptions
and source copies. The saved best/seed grammars and logs are preserved.

Optional rerun of the stochastic searches:

  g++ -O3 -std=c++17 logic_anneal.cpp -o /tmp/pa_brouwer_search
  /tmp/pa_brouwer_search brouwer_inputs.txt leaf_attrs.txt /tmp/pa_brouwer 360 2026111331
  g++ -O3 -std=c++17 brouwer_explosion.cpp -o /tmp/pa_brouwer_explosion
  /tmp/pa_brouwer_explosion brouwer_explosion_inputs.txt leaf_attrs.txt /tmp/pa_bexp 300 2026111332

Machine speed changes the proposal count reached before the time limit.
The supplied logs, exact best grammars and search_receipt.json record the
observed run; the saved result is not an exhaustive search certificate.

Attribution
-----------
The search engine, fixed physical rows and baseline grammars are inherited
from ProveIt commit 567266818aaeceb0f3a8f82debf303c8d84bddaf. See
PROVENANCE.json and ../../licenses/. The new work is the proposed head
replacement, corrected extra-head preparation, rejection argument and runs.
