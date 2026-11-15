# Primitive-recursive total clock for site 31

`PA194Site31CodedClock.clockCode : Code 13` sums the 19 explicit time terms used by the previously checked site-31 physical instruction. `codedRun` uses the PRA-model stepper composition law to collapse those nested calls to one run at the code's value, for arbitrary initial terms. `codedFrame` specializes this to the actual site-31 to site-32 physical frame equality from `PA194Site31Sentence.modelSentence`.

The 13 inputs are source registers 0–8, the independent controller tail, the gap parameter, the model-valued count of repeated one-spares, and the independent spare value. The frame result increments register 0, decreases the gap by one and adds one spare, retaining the other inputs. The required physical suffix is the model-length repetition ending in blank tape, exactly as in the prior site-31 native sentence.

This is an all-PRA-model single-instruction coded-clock theorem. It does not yet code the whole site-31–33 loop, establish model-length physical iteration or prove a consistency implication. The prior native iPRA equality concerns the nested-clock expression; transfer of this new coded-clock equality remains separate.

A fresh staged source replay passed with exit 0, both axiom audits and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site31-coded-clock.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site31-native-repo /dev/shm/pa194-loop-to32-coherent /dev/shm/pa194-site31-matched-coherent \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site31-coded-clock-replay
```

Use a fresh output directory. The checker rebuilds the new module, rejects conflicting direct machine-object overlaps and `sorryAx`, requires both axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier machine and foundation stages remain prebuilt; this replay does not independently authenticate their full transitive closures. The fetch machine-object root is excluded from Lean's search path.
