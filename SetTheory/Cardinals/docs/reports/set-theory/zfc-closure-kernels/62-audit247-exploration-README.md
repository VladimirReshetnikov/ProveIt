# Optional bounded bootstrap exploration

`boot_search.cpp` records how a safe blank bootstrap was found after the guarded state reduction. It is **not required** to reproduce the machine or verify its certificates. The default verifier uses only Python and replays the selected exact bootstrap directly.

From the package root, compile with a C++17 compiler and place the optional executable and output under `/tmp`:

```sh
c++ -O3 -std=c++17 exploration/boot_search.cpp -o /tmp/zfc-prefix247-boot-search
/tmp/zfc-prefix247-boot-search reference/prefix250_old.tm 10000000 > /tmp/zfc-prefix247-bootstrap-search.jsonl
```

The input must be the **original-label 250-state source**, not the final canonical table. The program installs the `60/read-zero → 20` reduction, excludes states 0, 1, and 3, and explores all 988 choices for the free initializer `97/read-zero`: 247 retained target states, two write symbols, and two directions. Each candidate initializer is installed throughout its run. The final numeric argument is the per-candidate transition cutoff.

The recorded run used a 10,000,000-transition cutoff, tape coordinates within ±1,000,000, and a root-header scan distance at most 100,000. It accepted a candidate only at state 96 with an empty PC, marker at `head−1`, distance at least 40, at least ten valid blocks, physical values 0 in slots 0, 2, and 7, and an exact support count excluding unparsed one-cells. It found 15 initializer choices reaching such a root. Missing hits are bounded-search outcomes, not impossibility results.

[../results/bootstrap-search.json](../results/bootstrap-search.json) retains the compact results and source hash. Its `selected` fields point to the current `code/check_boot_canonical.py` and `results/bootstrap-canonical.json`; the separately implemented dense replay is also part of the main verifier.

The final machine retains the original initializer `97 0 1 R 83`. It reaches its certified root after **741,241 transitions**. This choice keeps the change from prefix250 to one surviving-row redirection plus removal of three states. Some explored initializers reached roots sooner, but runtime optimization and initializer minimality are not claims of this package.

The search works in a finite tape array; the final sparse replay specifies the full infinite tape by its finite set of one-cells. The report's unbounded runtime argument rests on the register and instruction proofs after the verified root, not on the search cutoff or finite array.
