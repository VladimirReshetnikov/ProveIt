Bounded logical-emitter decoder searches
=======================================

Scope
-----
These searches did not produce an accepted machine with fewer than 194
states. They explore two additional emitter ideas, independently of the
accepted PA194QN result. A numerical allocation score alone is not a
complete transition-table correctness or consistency-equivalence proof.

Inputs
------
h5_search.txt replaces the equality-witness head
  exists x_D E(H,D)
with
  exists x_D E(A,D),
keeping the other heads, Gamma(A), guard and gate unchanged. The full axiom
family is identical since A,D,H can be independently selected. Only the
proof selector for this head changes. The input starts from the original
PA194 source association with the changed single copy-register token.

qd_CZD.txt combines the Q premise-exchange form of the sixth axiom with
Gamma(D) in place of Gamma(A). It includes two seed associations adapted
from Q and D, the cached-C fixed controls, the known-zero scheduler jump,
and the known-zero D decrement at the final AX return. These semantic
components have independent ordinary justifications; the particular
optimized combinations were not promoted to verified physical machines.

The template files include all fixed transition rows and complete source
trees needed by the search. No repository checkout, network or Python
module is needed to rerun these numerical searches.

How to rerun
------------
Compile with any C++17 compiler:

  c++ -O3 -std=c++17 search_adaptive.cpp -o search_adaptive
  c++ -O3 -std=c++17 search_closing_adaptive.cpp -o search_closing_adaptive

Then select output prefixes in a writable scratch directory:

  ./search_adaptive h5_search.txt leaf_attrs.txt /tmp/h5 180 202611140589
  ./search_closing_adaptive qd_CZD.txt closing_attrs.txt /tmp/qd 180 202611140591

A score of s corresponds to 134+s projected states. Compatible finite
history folds are jointly screened near the threshold. Scanner/address
penalties are reported separately. A zero-penalty score 60 would nominate
194 states, 59 would nominate 193, but exact source control flow, a complete
blank startup, and universal physical primitive simulation would still
require verification. Failed searches are not lower bounds.

The stopping condition uses wall time; the fixed seeds do not promise an
identical mutation count on another machine. Frozen best grammars and the
recorded logs bind the observations without needing rediscovery.

Attribution
-----------
The C++ search programs and screen.cpp are reused from ProveIt revision
3cc7fbf75ba111a0da696ef2f6001dd528891bd5, under
Computability/BusyBeaver/Research/PA/docs/pa194j_pa194d_conpa_2026-11-13/
research/search/. They in turn attribute the decoder-screening and
occurrence-search infrastructure to the earlier PA194C search/grammar
packet. License notices are retained. New work here is the h5 emitter
correlation, the Q+D combined source inputs, and this bounded execution.

Observed results
----------------
Both 180-second runs ended with best zero-penalty score 61 (195 projected
states). h5: 2,613,698 mutations; 70 readers and 9 folds. Q+D: 2,475,004
mutations; 69 readers and 8 folds. See search_results.json. Neither result
is promoted to a verified consistency machine, and neither implies a lower
bound for these source families.
