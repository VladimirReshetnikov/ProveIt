# Optional bounded initializer search

`seed_search.cpp` is the discovery utility that found the existing-state blank initializer. It is separate from the proof and is not required by `code/verify_all.py`.

With a C++17 compiler, from the package root:

```sh
c++ -O3 -std=c++17 search/seed_search.cpp -o /tmp/zfc-context246-seed-search
/tmp/zfc-context246-seed-search sources/prefix250_old.tm 3000000 core246
```

The `core246` mode applies the two entry redirects and considers the 246 retained states as possible blank starts. Its acceptance predicate recognizes an entire finite root frame with an empty program counter, head-to-header distance at least 40, nine primary blocks, a nonempty spare suffix, and zero formula fields. It produced:

```text
PASS mode=core246 w=1 d=1 target=95 steps=410735 h=-5 header=176 values=0,0,0,3,0,0,3,0,0, spares=167
DONE cases=246 passes=1 limit=3000000
```

The `w` and `d` fields are unused seed-mode options in `core246` mode. The program uses both a finite step cutoff and a finite tape array. A rejected start may run too long, leave the array, halt, or fail to reach this particular acceptance predicate before the cutoff. Rejection is not a mathematical impossibility result, and the search does not prove minimality or nonhalting.

The final bootstrap is independently replayed without using this search predicate by `code/check_bootstrap.py` and `code/independent_rebuild.py`, with complete equality of all one-cell positions checked. The mathematical report supplies the safe-root and unbounded simulation arguments.
