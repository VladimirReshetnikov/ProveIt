PA194AX11S decoder searches
==========================
The fixed part includes the symmetric controller fold before reader optimization.
Two supplied AX11 seeds retain the ordinary and exchanged sixth heads.
No effective reader score below 60 was obtained; 59 was required for 193 states.
Every candidate would still need source, physical and startup validation.

Reproduce with a C++17 compiler (run from this directory):
  c++ -O3 -std=c++17 search.cpp -o /tmp/ax11s-search
  /tmp/ax11s-search seeds.txt leaf_attrs.txt /tmp/run 360 202611141201
  c++ -O3 -std=c++17 search_permuted.cpp -o /tmp/ax11s-permuted
  /tmp/ax11s-permuted seeds.txt leaf_attrs.txt /tmp/permuted 360 202611141231

Time limits are wall-clock limits; proposal counts are not portable.
The supplied logs record the actual completed runs. This is not a lower bound.
Sources adapt the incoming AX11 search/search_plateau lineage; licenses are at
the packet root. search_permuted.cpp enables head permutations and changes the
annealing temperature. The only fixed-table change in seeds.txt is the new
AX11S symmetric controller allocation after its fold.
