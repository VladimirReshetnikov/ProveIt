# Exact short transition replacements

`local_rewrites.cpp` enumerates replacement actions for each old row, tests up to seven transitions, and exhausts every 15-cell tape pattern for preliminary survivors. Because seven transitions cannot read outside that window, a survivor has an exact local all-tape stuttering proof for its stated row and unchanged surroundings. The enumeration tested 369,371 alternatives and retained 64, all with maximum duration three. The extra alternative relative to 430 * 859 occurs because the old halt-target row has no identical alternative in the working-state target pool.

Reproduce from this directory:

```sh
g++ -O3 -std=c++17 local_rewrites.cpp -o local_rewrites
./local_rewrites ../baseline/k215/k215.native.tm 7 > replay_local_rewrites.txt
python3 fold_rewrites.py
python3 fold_two_sided.py
```

The two Python searches test marker folds after these local repairs and write new `replay_*.json` files. Frozen result lists are empty. These are restricted local construction searches, not a global lower bound. `baseline-engine-row-audit.json` is an additional historical row-use classification; its broader internal-row definition was not adopted as an allocation constraint.
