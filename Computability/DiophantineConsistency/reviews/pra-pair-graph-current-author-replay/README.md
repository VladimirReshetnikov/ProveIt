# Candidate-PRA model pairing replay

The four source/check pairs establish that each candidate-PRA model has an
IOpen arithmetic reduct, and hence that its mapped bounded pairing graph
contains a pair for any two elements, uniquely determines its components, and
bounds each component by the pair plus one. This is a model-theoretic pairing
result; it does not prove full IΣ₁ conservation or provide a primitive
recursive pairing code.

The replay manifest SHA-256 is
`5df1fcff552ecbbe98255690e4b26507a8c8d097811e7f5bec64397a4b91aa3f`.
The author and private runs passed, and the root's independent replay passed at
`/tmp/pra-pair-graph-current-independent-g0uvduvp`, with source, object and
full-log hashes matched against the manifest. Its parent was
`/tmp/parsons-bounded-post-fixed-independent-5pukvc5y/lib`, independently
replayed over the accepted 31-module post-fixed-merge provider. The replay
checks the listed parent source/object pairs and builds all eight local modules;
Foundation, Mathlib and the remaining inherited Parsons artifacts are outside
this focused replay's authentication boundary. The earlier manifest's statement
that the upstream 31-module replay was pending is superseded by that independent
PASS.

Reproduce with:

```sh
python Computability/DiophantineConsistency/reviews/pra-pair-graph-current-author-replay/replay.py --parent /tmp/parsons-bounded-post-fixed-independent-5pukvc5y/lib
```
