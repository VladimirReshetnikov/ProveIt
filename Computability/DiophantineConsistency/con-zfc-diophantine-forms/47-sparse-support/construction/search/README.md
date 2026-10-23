# Optional finite weight search

The two C++17 programs use deterministic random seeds and simulated annealing.
They search only finite integer ranges. They are discovery tools; the release
proof relies on exhaustive checking of the literal vectors.

Run from this directory, for example:

```sh
g++ -O3 -std=c++17 search.cpp -o search
./search 120 60
g++ -O3 -std=c++17 search_full.cpp -o search_full
./search_full 221 60
```

The first search isolates the39 used quadratic pairs and then translates all
31 variable weights above their span, isolating the linears automatically.
Its delivered result is weights120.json, with W=239. The second search
explicitly includes padding index0 and isolates all71 supported monomials.
Its delivered result is weights_full221.json, with W=220. Index0 is not a
source variable. Runtime limits and platform details can affect whether a
result is reached during a given run. No search optimality claim is made.
