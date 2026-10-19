# Selected search artifacts

These programs are **discovery tools**, not the acceptance criterion for the 240-state machine. The separate source proof, small four-state invariant, whole-tape checks, exact initialization, and complete final runtime replay certify that artifact.

## Reproduce the successful finite search

With a C++17 compiler, from this directory:

```bash
g++ -std=c++17 -O3 coupled.cpp -o coupled
./coupled 31 ../reference/rotated241_old.tm
```

The positive row is:

```text
72 90 0 -1 144 1 -1 36
```

It means: retain 72, delete 90, choose `(write0,left,target144)` for read 0 and `(write1,left,target36)` for read 1, and redirect incoming targets through the state map. The universal window invariant is computed from an arbitrary initial tape at state 95. Local comparisons require the mapped old one-step endpoint, positive duration and no premature halt. The full two-row check rechecks both synthesized transitions together, including revisits to the retained state.

The search only accepts certificates within the configured radius and duration. Its negative result on the unrotated baseline does not prohibit a different simulation or source transformation. The explicit short proof in the report is simpler than the discovery invariant and is verified independently.

## Root's alternative finite search families

Generate the baseline's radius-three domains:

```bash
python3 derive_domains.py --output-dir .
```

Then compile and run:

```bash
g++ -std=c++17 -O3 offset_synthesize.cpp -o offset_synthesize
./offset_synthesize ../reference/baseline241_old.tm domains.txt

g++ -std=c++17 -O3 complement_synthesize.cpp -o complement_synthesize
./complement_synthesize ../reference/baseline241_old.tm domains.txt

g++ -std=c++17 -O3 stuttering_search.cpp -o stuttering_search
./stuttering_search ../reference/baseline241_old.tm 4
```

The first family maps one deleted state's head two cells left or right, reverses the direction of each incoming edge, and synthesizes both retained rows under a sufficient no-internal-revisit criterion. Its recorded search has 52,560 pairs and 69,580,800 tested row actions, with no survivor.

The second family complements a predecessor cell in the deleted state's configuration relation, adjusts incoming writes accordingly, and synthesizes retained rows under the same sufficient criterion. Its recorded search has 52,560 pairs and 50,457,600 row actions, with no survivor.

The third permits positive old and new blocks to join, with a bounded footprint and duration, and chooses retained rows from the old pair's rows. At radius four and maximum 32 steps it tests 115,680 overlays, with no survivor. This variable-block control did not synthesize arbitrary new rows.

`offset_search_result.json` records an earlier, still narrower direct-offset control with no new retained-row synthesis. It is retained as a historical receipt; the generalized source above subsumes its intended diagnostic role, not its exact implementation.

Each statement concerns the specified finite family. No negative result here is a semantic lower bound or a minimality theorem.
