# Discovery of the 236-state construction

The new reduction is the single base fold

```text
BASE 182 223 0 -1 198 1 -1 210
```

It retains inherited state 182, deletes 223, redirects every target 223 to
182, and assigns the retained rows `0 L 198` and `1 L 210`. No helper row is
changed. Its input is the **source-rotated 237-state table**, whose SHA-256 is
`da0b3d1fdd74d56482b9d231119bbbaccdbcadc78e7b7df72c3a734a3a808724`.
The same fold is not valid on the earlier unrotated 237-state table.

## Fast finite discovery replay

With a C++17 compiler, run from this directory:

```sh
c++ -O3 -std=c++17 empirical_contexts.cpp -o empirical_contexts
c++ -O3 -std=c++17 plain_folds.cpp -o plain_folds
./empirical_contexts input237_rotated.tm sites.txt 5 replay_profile.txt
./plain_folds input237_rotated.tm replay_profile.txt
```

The expected final standard-output line is exactly the `BASE` line above.
The delivered replay examined all 27,966 state pairs and 52,799,808
synthesized row choices and found this one candidate. It took approximately
six seconds for the fold search on the research machine; timings are not
part of the mathematical claim.

The finite profile starts with the blank initializer, then executes all
6,455 ordered source instructions with four register fixtures and both
guards for conditional decrements. It has 33,545 runs, 18,833,956 literal
steps, and 28,582 distinct state/window observations of radius five.
The search compares positive old/new paths of at most 65 steps while they
remain inside those windows.

## Original broader discovery run

The original discovery used the older one-helper search as well:

```sh
c++ -O3 -std=c++17 neutral_domains.cpp -o neutral_domains
c++ -O3 -std=c++17 helper_domains.cpp -o helper_domains
./neutral_domains input237_rotated.tm 5 5 65 65 replay_profile.txt > replay_neutral.txt
./helper_domains input237_rotated.tm 5 5 65 65 replay_neutral.txt replay_profile.txt
```

It found the base fold above plus 75 optional helper variants. All 76
records use the same base fold; the construction takes the version with no
helper edit. The broader run examined 654,121,399 helper choices. The
delivered `full_search.txt` and `full_search.log` retain its complete output.

## Why the accepted reduction is a theorem

The finite profile is an underapproximation of reachable tape contexts and
is used only to discover the candidate. The proof subsequently establishes
two syntactic invariants from every initial binary tape at state 95:

- An old configuration in state 182 has a 1 immediately left of the head.
- An old configuration in state 223 has a 0 immediately left of the head.

The unique incoming transitions establish these invariants immediately.
Each of the four old rows at these two states is simulated by exactly
three new steps. Those steps read only the current bit and that known left
neighbor, and every write preserves its previous value. All other 470 old
rows commute through the state map in one step. Thus the whole tape and
head agree at each synchronization point, with positive clock
`tau(t) = t + 2*N(t)`, where `N(t)` counts old visits to 182 or 223.

The separate local checker, startup checker, source rotation certificate,
and unbounded affine/list runtime certificate establish the accepted result.
No empirical coverage assumption is used in the final halting equivalence.

## Attribution

`empirical_contexts.cpp`, `neutral_domains.cpp`, and `helper_domains.cpp`
are unchanged copies of the discovery programs supplied with the inherited
`zfc237-research-20261019` archive. That archive attributes their origin to
the earlier ProveIt incoming `BusyBeaver239_Research_2026-10-19.zip` research.
`plain_folds.cpp` is a reduced and input-validated replay of the base-fold
part of that search, prepared for this construction. Machine/source credit
and license notices are retained by the enclosing research deliverable.

`receipt.json` pins the table, profile, scripts, outputs, and finite search
scope. These restricted searches establish no lower bound on possible
Turing-machine state counts.
