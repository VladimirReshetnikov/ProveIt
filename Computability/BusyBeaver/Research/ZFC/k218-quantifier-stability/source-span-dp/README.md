# Calibrated K/S+QS: bounded source association

The search found a **208-node source**, with 5,152 primitive leaf occurrences, zero-run bound 6 and depth 38. This improves the earlier valid-zero-bound 221-node source pricing. It does **not** improve the primary binary machine: all four best sources were rejected by both existing allocators. The primary218 source has 205 nodes and 4,744 leaves.

The exact calibrated K/S+QS forms replace the old closed rho8 forest [135,486), giving twelve axiom outputs. The source dynamic program shares 91,002 token intervals across all 1,296 parameter-permutation/order recipes. It retains two candidates per leading-zero depth, accounting for shared subtree identities. Processing all intervals took 9.18 seconds. The found cost is a beam-search result, not a proved grammar optimum.

All 16 retained sources pass complete primitive-word and guarded-CFG checks, including all 4,393 unchanged instruction sites and the first 37 startup source rows. The [independent review](peer/review.json) additionally checked every exact formula AST and used a third CFG resolver. [Frozen evidence](evidence/README.md), [successful source checks](evidence/verified-result.json), [rejected global allocations](evidence/global-allocations/result.json) and the [exact placement map](publication.json) preserve the full scope. No primitive runtime or startup was replayed. Later allocator diagnostics are separate from this packet.

Reproduce from a fresh scratch directory, using a repository checkout with the pinned primary218 files:

```sh
python3 -B prepare_replay.py --repo /path/to/Proofs --out /tmp/qs-span-replay
cd /tmp/qs-span-replay
python3 -B prepare.py > prepare.stdout.log 2> prepare.stderr.log
g++ -O2 -std=c++17 dp.cpp -o dp
./dp < input.txt > dp-result.json 2> dp.stderr.log
python3 -B check_candidates.py > check.stdout.log 2> check.stderr.log
python3 -B global_allocations.py > global.stdout.log 2> global.stderr.log
```

The preparation helper copies the frozen code and changes only its repository-path literal; it runs no search. The optimizer has a 120-second internal cap. The original complete search, source checks, allocator identity controls and failures remain unchanged in `evidence/`. The independent review preserves its own initial parser typo and corrected successor.
