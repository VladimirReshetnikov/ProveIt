# Supplementary bounded search on the other 239-state branch

This optional experiment searched the final **Coordinated239** machine for another reduction. It found no candidate in the implemented finite-window family. Its input is a different 239-state table from the Boundary239 input used to construct M238. This negative experiment is separate from the successful M238 acceptance proof and is not a lower bound.

The portable sources are unchanged copies of the three C++ programs from the preceding `BusyBeaver239_Research_2026-10-19.zip` archive. `PROVENANCE.json` gives the exact archive identity, original paths, input hashes, and the conversion from its ordered source triples to `inputs/sites.txt`. The source table has 239 working states, inherited start 95, dispatcher 96, and separate halt 254. Applicable inherited notices are retained in the main package’s `licenses/` directory.

## Reproduce

A C++17 compiler and the standard C++ library are required. Run the following commands from this `discovery/` directory. They write only into a new `replay/` directory. Use another output-directory name if preserving a previous experiment.

```sh
mkdir replay
c++ -O3 -std=c++17 empirical_contexts.cpp -o replay/empirical_contexts
c++ -O3 -std=c++17 neutral_domains.cpp -o replay/neutral_domains
c++ -O3 -std=c++17 helper_domains.cpp -o replay/helper_domains
replay/empirical_contexts inputs/baseline239_old.tm inputs/sites.txt 5 replay/profile239_r5.txt > replay/profile239_r5.out 2> replay/profile239_r5.log
replay/neutral_domains inputs/baseline239_old.tm 5 5 65 65 replay/profile239_r5.txt > replay/neutral239_r5.out 2> replay/neutral239_r5.log
replay/helper_domains inputs/baseline239_old.tm 5 5 65 65 replay/neutral239_r5.out replay/profile239_r5.txt > replay/helper239_r5.out 2> replay/helper239_r5.log
```

The final helper output is empty in the recorded run, while its stderr log ends with `candidates 0`. The neutral proposal file contains 601 proposals. Its complete recorded contents are retained, so proposal generation can be compared independently of the final search. Runtime figures depend on the compiler and computer; all combinatorial counts below should be identical for these exact inputs and commands.

## Implemented scope and recorded result

The profile generator runs all 6,455 source leaves from a fixed collection of finite valid register frames, splitting conditional decrements into zero and positive cases, plus the exact blank initialization. It records the local eleven-bit window from head−5 through head+5 whenever a state is visited. Bit zero represents head−5. This gives an **underapproximation** of future execution contexts; it is not a universal invariant.

| Recorded quantity | Value |
|---|---:|
| Finite runs including blank initialization | 33,545 |
| Literal transition steps in the profile | 18,773,340 |
| Distinct represented state/window pairs | 28,308 |
| Individually neutral helper-row proposals | 601 |
| Unordered state pairs tested | 28,441 |
| Base row choices tested | 54,151,664 |
| Helper checks | 664,870,372 |
| Context tests | 1,457,896,363 |
| Accepted candidates | 0 |
| Recorded final search time | 150.227 seconds |

The neutral pass searches for a changed transition row that preserves behavior in all represented original contexts, permitting synchronization after positive blocks of at most 65 old and 65 new steps. The coupled search attempts to reuse one unordered pair of states while applying one of those individually neutral helper-row edits. It allows the paired rows to be synthesized jointly, subject to the implemented partial-trace pruning. Synchronization requires the mapped state, the same head position, and equality of every represented tape bit. Candidate traces must remain inside the finite read/write footprint up to synchronization.

These are the implemented search bounds and search family, not a theorem that no 238-state machine can arise through related ideas. The search does not exhaust other source layouts, contextual splitting into several roles, multiple coordinated helper changes, larger footprints or longer synchronization blocks, or alternative mathematical formalisms. A survivor would still need an independent universal context proof and blank initialization check. No survivor was obtained, so this experiment supplies no additional machine used by the main proof.

## Recorded artifacts

`recorded/search239_receipt.json` summarizes the result and its limitations. The three `.log` files are the actual new execution logs. `recorded/neutral239_r5.out` contains the 601 helper proposals, and `recorded/helper239_r5.out` is the empty final candidate stream. Compiled binaries and the regenerable 28,308-line profile are intentionally omitted.

The original table, source, sampler, and search method are inherited work. This task contributes their execution on the final Coordinated239 table, the recorded outcome, and its inclusion as a reproducible supplemental negative experiment. No state-minimality or historical-priority claim is made.
