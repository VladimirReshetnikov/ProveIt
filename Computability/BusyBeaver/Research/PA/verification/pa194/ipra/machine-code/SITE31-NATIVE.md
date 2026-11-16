# Native iPRA physical site-31 increment

`PA194Site31Sentence.nativeIPRA` proves, in the existing `IPRAStandardTheory.standardTheory`, the universally closed equality of two explicitly constructed primitive-recursive terms. Its 13 inputs are source registers 0 through 8, the remaining controller file tail, the gap parameter, the number of one-spares, and the independent spare value. The left side runs the literal encoded PA194 stepper through the site-31 physical increment using explicit finite nested PR clock terms. The right side is the exact site-32 physical frame: register 0 increased by one, the gap shortened by one, and the count of one-spares increased by one; all other inputs are preserved. The input suffix is the model-length one-spare repetition ending in blank tape. The theorem is unconditional for these inputs. The controller source position embedded in the packed frame supplies register readers; the separate physical control header is site 31 or 32.

The sentence is a physical instruction result in native iPRA, not a statement of the complete physical/source simulation or either direction of Con(PA) versus nonhalting. `modelSentence` proves it in every PRA model, `classicalPRA` transfers it to classical PRA, and `nativeIPRA` uses the existing equality transfer to the exact standard theory; Lean's three printed axiom audits include no `sorryAx`.

The five small semantic modules check the term encodings of vectors, clock, nested run, and input/output frames separately, and the final module composes them with `PA194Site31PhysicalClock.frameStep` and the checked source-frame correspondence. The source replay builds those modules and the repository's `PA194ModelLoopFrameAt` in a fresh output:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site31-native.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-loop-to32-coherent /dev/shm/pa194-site31-matched-coherent \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site31-native-replay
```

Use a fresh output directory. This replay checks direct machine-import overlaps, records the direct prebuilt objects, their available Lean companion artifacts, seven source hashes and four upstream receipts before and after, rejects `sorryAx`, and requires all three final axiom reports. It consumes the documented physical-loop, matched, tail, carry, machine-baseline and foundation stages as prebuilt; receipt hashes and direct-object checks do not independently authenticate their complete transitive object closures. It does not place the fetch machine-object root on the Lean search path; only its documented general `foundation-view` is used.
