# K/S plus mixed commutation: bounded source pricing

The search found a **209-node source**, with 5,057 primitive leaves, zero-run bound 6 and depth 38. It emits eleven axiom outputs: K/S replace rho8 and `M(i,j,A) = Q_i NN(Q_j A) → NN(Q_j(Q_i A))` replaces rho4. The remaining literal rows and gates are unchanged. The [ordinary calibration](../proof.md) is separate from these encoding measurements; no new Lean or binary-machine result is claimed.

The family contains 432 pairs of parameter-permutation/order recipes. The first two-splice attempt was unusable: literal pruning left a fixed suffix with twelve consecutive zeros. That attempt is retained. A successor widened the rho4 splice to its closed enclosing subtree [648,4433), preserving its primitive prefix and suffix while re-associating closed factors. A finer bounded successor also updated the fixed-base cost and exposed another closed layer. Both found 209 nodes; neither is an exhaustive grammar optimum.

Each successor's 16 retained sources passes exact K/S/M formula AST checks, whole primitive-word equality, two full CFG resolvers, all 4,094 unchanged instruction sites' guarded edges and the unchanged first 37 startup rows. See the [first valid search](evidence/joint-v2-result.json), [finer search](evidence/joint-v3-result.json), [source validation](evidence/verified-v3-result.json), [full frozen account](evidence/README.md) and [placement map](publication.json). No allocator, primitive runtime or startup was invoked in this packet; subsequent root allocator diagnostics are separate.

Reproduce in a fresh scratch directory:

```sh
python3 -B prepare_replay.py --repo /path/to/Proofs --out /tmp/mixed-span-replay
cd /tmp/mixed-span-replay
python3 -B prepare.py > prepare.stdout.log 2> prepare.stderr.log
g++ -O2 -std=c++17 dp.cpp -o dp
./dp < input.txt > dp-result.json 2> dp.stderr.log
python3 -B joint.py > joint.stdout.log 2> joint.stderr.log
python3 -B joint_v2.py > joint-v2.stdout.log 2> joint-v2.stderr.log
python3 -B check_candidates_v2.py > check-v2.stdout.log 2> check-v2.stderr.log
python3 -B prepare_v3.py > prepare-v3.stdout.log 2> prepare-v3.stderr.log
./dp < input-v3.txt > dp-v3-result.json 2> dp-v3.stderr.log
python3 -B joint_v3.py > joint-v3.stdout.log 2> joint-v3.stderr.log
python3 -B check_candidates_v3.py > check-v3.stdout.log 2> check-v3.stderr.log
```

The preparation adapter changes only the repository-path literal and executes no computation. Inner search caps are 120 seconds initially and 30 seconds for the finer pass; the outer factor search has a 120-second cap. The finer actual pass took 13.10 seconds for 653,232 outer joins and 62,208 complete-source beam combinations. Historical status strings written before the ordinary calibration review remain unchanged in the raw evidence.

An [independent source review](peer/review.json) checked all 78 exact formula
recipes and all 32 saved sources across both valid passes. Its own reader
reconstructed every whole-source CFG by checking the two closed replacement
intervals and all 4,094 unchanged rows, as well as the literal words, complete
metrics and first 37 startup paths. It found no defect. This review did not
execute the search, allocator or runtime; [its source](peer/review_static.py)
and [tree reader](peer/tree_reader.py) are retained unchanged. The reader's
original scratch paths bind the reviewed snapshots; it is a review record,
while the preparation adapter above supplies the portable search reproduction.
