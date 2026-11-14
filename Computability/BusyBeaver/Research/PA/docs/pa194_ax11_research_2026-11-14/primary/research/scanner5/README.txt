Five-zero scanner investigation (rejected)
=========================================
The supplied outer source rotation preserves the complete 3,673-instruction
source graph but the nominal 193-state table fails 52 of 4,780 universal
primitive outcomes. Three of those are fixed-pop dispatch failures caused
by changing the predecessor bit. Most others concern six-zero AX paths.
A fresh replacement-action screen repaired the fixed-pop probes in three
ways, but each replacement then failed eleven AX source outcomes; there
was no accepted repair. The companion shorter-scanner grammar search tried
1,351,175 proposals and accepted 111,280 moves over 180.01 seconds. Its
best score remained 64 = 60 effective AX readers plus a scanner penalty4.
No five-zero-valid 193-state machine was obtained.

The raw grammar search is reproducible with:
  c++ -O3 -std=c++17 search5.cpp -o /tmp/scanner5-search
  /tmp/scanner5-search seed5.txt leaf_attrs.txt /tmp/scanner5 180 202611140919

This optional negative evidence is not a lower bound. The successful
PA194AX11 machine retains the existing scanner and changes the AX protocol.
