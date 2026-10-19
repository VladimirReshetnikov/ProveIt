# Discovery of the new 237-state reduction

This directory records the finite discovery search that produced the newly
proved merge `235 -> 98` with a coordinated change to helper row `240/1`.
The accepted proof is in `../sections/fold237.tex` and `../verification/verify_237.py`.
It does not infer any invariant or nonhalting claim from this profile.

The input is the exact composed 238-state machine, retained as `input238.tm`.
Its calibrated instruction list is `sites_logical.json`; `sites.txt` is the
same list in the C++ profile program's input format. A `CH` instruction's
unused argument is represented by `0` in this text format.

Compile and reproduce from this directory with a C++17 compiler:

```sh
c++ -O3 -std=c++17 empirical_contexts.cpp -o empirical_contexts
c++ -O3 -std=c++17 neutral_domains.cpp -o neutral_domains
c++ -O3 -std=c++17 helper_domains.cpp -o helper_domains
./empirical_contexts input238.tm sites.txt 5 replay_profile.txt
./neutral_domains input238.tm 5 5 65 65 replay_profile.txt > replay_neutral.txt
./helper_domains input238.tm 5 5 65 65 replay_neutral.txt replay_profile.txt > replay_helper.txt
```

The expected final output is exactly:

```text
HELPER 240 1 1 -1 87 FOLD 98 235 0 -1 240 1 1 16
```

The helper changes `240/1` to write 1, move left, and enter 87. The fold
retains 98, deletes 235, redirects old targets 235 to 98, and gives retained
98 the rows `0 L 240` and `1 R 16`. Its read-1 row is already present in the
input. The resulting machine is `../zfc_composed237_old.tm`.

The profile runs every source instruction with four concrete register
fixtures and both guards of each conditional decrement, plus the blank
startup. It collects 27,995 state/window pairs in 18,811,196 literal steps
across 33,545 runs. These windows underapproximate future reachable contexts.
The search considers both synthesized rows of each merged state and one
helper row that is individually neutral on the finite old profile. It finds
one candidate after 28,203 state pairs and 669,196,927 helper checks.

The later proof is stronger than this discovery process. It verifies an
inductive predecessor invariant for arbitrary initial tapes from state 95,
and three exact local blocks that never inspect an unconstrained cell and
preserve the entire tape. No empirical context-coverage assumption survives
in that proof.

`receipt.json` pins the inputs, scripts, profile, logs and output. The elapsed
time is environment-dependent; it is not part of the mathematical claim.
`coordinated239_negative_scope.json` records an earlier unsuccessful run of
the same restricted search family on the other 239-state candidate. Neither
search establishes a lower bound on all possible binary machines.

## Attribution

The three C++ programs are unchanged copies of the discovery programs in
the earlier ProveIt incoming archive `BusyBeaver239_Research_2026-10-19.zip`,
under `research/search/head_offset` and `research/search/local_folds`.
Their existing notices and the underlying machine/source attribution are
retained by the enclosing deliverable. The new result is the application to
the composed 238-state decoder, the resulting 237-state table, and its
unconditional local simulation proof.
