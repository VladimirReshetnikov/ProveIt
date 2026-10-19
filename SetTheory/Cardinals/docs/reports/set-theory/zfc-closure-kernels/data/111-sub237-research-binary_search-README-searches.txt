SEVEN COMPLETED FINITE DISCOVERY SEARCH FAMILIES

These searches returned zero candidates in their stated finite families. They do not prove a lower bound or exhaustion of general binary-machine transformations. The empirical profiles underapproximate reachable configurations; a discovered candidate would need a new inductive simulation proof.

From this directory:
  python3 -B replay_binary_search.py
checks the exact input hashes without rerunning a search.

  python3 -B replay_binary_search.py --profiles --output /tmp/zfc-profile-replay
regenerates all three finite profiles and all neutral-substitution lists, comparing exact bytes with the delivered data. Use a fresh output directory.

  python3 -B replay_binary_search.py --full --output /tmp/zfc-search-replay
also compiles and reruns all seven searches, comparing all deterministic final counters and all candidate outputs. Full replay takes tens of minutes depending on the CPU. Python3.10+ standard library and a GCC-compatible C++17 compiler are required. No network, Lean or theorem prover is needed.

search_summary.json records each family, its exact finite scope and its completed counters. The constrained source profile uses the K16 product annotations proved separately in research/source_abstraction. It includes the exact blank initializer and six valid primary-register fixtures per permitted source guard.

The additional tag/offset scripts from a separate audit branch have their own retained logs and are outside the seven-family replay; they are not silently claimed by this receipt.
