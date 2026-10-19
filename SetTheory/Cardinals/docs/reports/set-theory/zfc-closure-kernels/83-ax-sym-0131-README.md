# Failed local detector synthesis: diagnostic record

This optional C++ search attempts to replace the eight-state restoring detector with seven local states. **No model met all nine contracts; no consistency machine or sub-246 result is supplied here.** The report records the two observed finite-search counts. `results.json` preserves those counts and the best per-contract scores; repeated models are possible.

The source checks finite tape cylinders and rejects an active read outside the known interval immediately. It does not assume that exterior cells are blank. The second mode may enter specified existing scanner states. Every local attempt must still restore the entire known tape and meet the stated return convention. Such local contracts alone would not certify a whole blank-tape consistency machine even if a successful detector were found.

To repeat an optional search on a disposable result path, using a C++17 compiler:

```sh
g++ -O3 -std=c++17 detector_search.cpp -o /tmp/zfc-detector-search
/tmp/zfc-detector-search 120 96 /tmp/zfc-detector-plain.json
/tmp/zfc-detector-search 120 96 /tmp/zfc-detector-borrowed.json borrowed
```

Time-based stopping and platform-dependent C++ library behavior can change the exact evaluated count and returned model. A local successful score would need independent verification and integration. A failed score is only a rejection under these contracts and fuel.

The shipped source is the final session version, which adds the borrowed-scanner mode while preserving the plain search behavior. The earlier plain best-result file predated the added `borrowed_existing_states` output field. No failed transition table is presented as a candidate machine. The source was written for this investigation; the contract design and original detector retain the attribution given in the main NOTICE and the prior incoming reports.
