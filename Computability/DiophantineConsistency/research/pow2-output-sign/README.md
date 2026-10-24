# Recover the actual pow2 output sign:73 source predicates

This fresh research packet omits raw104>=0 from the accepted74-predicate
source. It retains70 original scalar predicates plus V>=1, the paired
index-slack product, and f>=2. No projected equation or variable count
is claimed.

The actual source gives f*(raw104+2)=M+raw131+2>=3, so raw104>=-1.
The modified prefix skips its sole prefix use, row88, and the74 proof's
row114. The actual frame rewrites as W=(raw104+2)+sum(other42 arguments).
It still bounds every base/index and all other outputs, with |raw104|<W.
Under the only possible negative case raw104=-1, the actual indices
t and k122=t+1 are consecutive. Supporting calls0/9 recover those
paired seed bounds and signs, and actual call2 contradicts raw104=-1
by a positive residue below its modulus. No local factorial or other
power meanings precede this sign recovery. The source body stays fixed
in both existence maps.

`PROOF.md` gives the ordinary unbounded proof. `CERTIFICATE.json` and the
independent focused checker bind the complete actual rows,641-coordinate
prefix,429 strict steps, weak frame, exact calls/seeds, and source guards.
No optimizer, source builder, historical emitter or Lean is executed.

```sh
python -B Computability/DiophantineConsistency/research/pow2-output-sign/check.py --output /tmp/pow2-output73-normal.json
python -B -O Computability/DiophantineConsistency/research/pow2-output-sign/check.py --output /tmp/pow2-output73-optimized.json
```

The ordinary result is a73-predicate source equivalence. Actual projected
sizes require a separate materialization and independent checks.
`PEER_REVIEW.md` records the independent unbounded branch review and its
verification scope. The two normal/optimized receipts and their complete
transcripts are sealed with the proof, certificate and source bindings.
