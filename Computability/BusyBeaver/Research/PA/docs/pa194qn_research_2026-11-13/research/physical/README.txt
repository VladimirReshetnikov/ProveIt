Finite local contraction searches on PA194HS

These completed negative searches are optional research, not part of the
PA194QN proof and not a state-count lower bound. The scanner propagates a
conservative finite window from the blank start and admits both possibilities
for each newly exposed boundary cell. The 64-step contraction comparison
requires the simulated segment to remain inside that window.

Compile and reproduce from this directory:
  c++ -O3 -std=c++17 context_fold_scan.cpp -o /tmp/pa-local
  /tmp/pa-local PA194HS.native.tm 6
  c++ -O3 -std=c++17 context_fold_guard.cpp -o /tmp/pa-guard
  /tmp/pa-guard PA194HS.native.tm 9

See structural_search_receipt.json for exact counts and code provenance.
The first C++ source is inherited from the pinned PA194ZR structural search;
the second adds the restriction that one merged control is native68.
Licenses are retained in ../../licenses.
