# Native moment first returns

This implementation targets ProveIt commit
`704600626606a9097cfd89d4e3d2bbc63c8dd1cb` and the maintained
`Topology/UnknotRecognition/fast/fastunknot` API.  It compiles an actual
parallelity free-edge packet into one scalar weighted census, including
exact edge ownership and local fibre transport.  It does not expand normal
coordinates, boundary edges, or the corner namespace.

## Entry points

`native_moments.normal_parallelity_moment_words(triangulation, coordinates,
codec='pair', record_certificate=True)` accepts the same source data as
the maintained native boundary-word compiler.  It returns the complete
cyclic interface and an independently replayable source-bound certificate.
Each gap has the additional integer field `unmarked_edges`; removing that
field gives exactly the existing native output contract.

`native_moments.moments_from_parallelity_packet(triangulation, coordinates,
parallelity_certificate, codec='pair', record_certificate=True)` first
authenticates a full existing normal-cut parallelity packet and then runs
one **new** census.  It also binds active loops to certified base-profile
owners and retains passive boundary counts, including multiplicities of
unported profiles.  Replaying the upstream packet's four proofs is
additional work, not part of the one-new-census count.

The independent checkers are `verify_native_moment_words` and
`verify_native_moment_packet` in `native_moments_verify.py`.  They reconstruct
source geometry through the maintained reference path and do not import the
new producer, query builder, decoder, or word traversal.  They use their own
query construction, moment arithmetic and permutation traversal.  Incomplete
discovery returns `INCONCLUSIVE` with no skeleton or certificate.  Malformed
proofs return false; cancellation and invalid-source exceptions propagate.

## Two codecs

The default `codec='pair'` uses `r=4p` lifted endpoint labels and powers of two

```
A = 2 ** bit_length(2*r)
s_i = i + A*i*i
D = 2 ** bit_length(2*(r + A*r*r))
```

It adds `s_i` at terminal `i` and `D` at each canonically owned original edge.
After `length, remainder = divmod(weight, D)`, a nonzero remainder splits as
`squares, total = divmod(remainder, A)`.  Its two roots are recovered by the
integer-square-root identity.  The source degree-two theorem proves that the
sum of two labels never carries across either radix.

The retained `codec='four'` uses the incoming global count/sum/squares/length
packing.  The complete outputs of both codecs were compared on all 157
inherited source cases.  The pair codec reduces the scalar bound from
`O(N*p**9)` to `O(N*p**3)` and avoids the explicit count coordinate.  All
weights still have logarithmic binary length.  Neither producer nor checker
reconstructs large endpoint masks after decoding.

The global-inventory lemma supplies an additional arithmetic safeguard:
zero-label orbits have zero remainder, and singleton-label orbits would
decode roots `0,i`, which are rejected.  Every accepted row therefore
consumes at least two actual labels.  An exhaustive disjoint decoded matching
has `r/2` such rows and consumes all `r` labels, forcing exactly two per row.
This is not a proof that arbitrary two-label graph components are geometric
paths or that arbitrary integer masses count edges.  Those facts come from
source authentication and the canonical ownership construction.

## Reproduction

Place `Topology/UnknotRecognition/fast` and this `code` directory on
`PYTHONPATH`.  The research fixtures also use
`normal_orbit_research/fixtures.py` from the same pinned runtime.  Then run:

```
python -m unittest discover -s tests -p 'test_native_moments*.py' -v
python code/native_moments_benchmark.py --repeats 5
python code/native_moments_replay.py
```

The native suite covers 157 source cases and independent literal path lengths
on 146 of them, including five cap-only sources, 3420 point gaps and 219
positive gaps.  A separate geometric regression handles the one-edge loop
case, which does not occur in the source bank.  Binary tests use multiplicity
`2**16384`.  The arithmetic suite enumerates all 4140 partitions of eight
labels and accepts exactly the 105 perfect matchings.

Benchmark samples alternate the existing native compiler, the pair codec,
and the four-field codec, reversing their order on alternate repetitions.
Each implementation gets an untimed warmup.  Timed calls rebuild the complete
source query and produce certificates; independent replay is timed separately.
The output includes every sample, structural counts and certificate sizes.
Discovery and replay performance is instance-dependent: adding exact edge
mass can increase weight runs and can slow replay despite removing a census.

## Scope

The operation authenticates first returns, local port charts, fibre transport,
cyclic order, attachment type, and exact original-edge lengths.  It does not
supply coherent orientations across different boundary circles of a common
base, arbitrary markings inside a positive-length gap, new cutting surfaces,
or a complete unknot-recognition algorithm.  The weighted AHT theorem gives
a polynomial algorithm for the encoded orbit task.  The present measurements
do not prove a uniform polynomial bound for every trace or weight-run count
of the maintained Python implementation.
