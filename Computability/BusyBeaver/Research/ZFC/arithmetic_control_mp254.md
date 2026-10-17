# Complete actual MP branch in internal arithmetic

`ArithmeticControlMP254` proves the entire actual MP branch, from entry 6367
to fetch 0, for every internal file in every model of IΣ₁ with
scratch1=scratch2=0. It compares `wim(old TW, old param1)` with the old cache.

- Equality sets TW to old param1 and WS to `cantor(0, old WS)`.
- Inequality sets TW to 0 and preserves WS.
- Both cases clear the cache, return both scratch fields to 0, and preserve
  param1, AC, NP and PL.

The theorem starts after parameter decoding, so param1 already stores d+x.
Its exact equality test and zero filler agree with Enum254.cstep,
L2Control254.mp_branch and ArithmeticCommandStep254.effectValue. A second
theorem adds the actual one-step AC=0 classifier with the same complete-file
endpoint.

The proof composes the checked initial parameter push/short unpair, a newly
bound actual constructor PairShape, a fourfold transfer, the actual TW-to-
scratch1 transfer, and the checked comparison/success tail. The fourfold
transfer has six instructions per positive iteration and a final zero test:
its exact logical clock is `6*old scratch2+1`. It adds four times the original
scratch2 to TW and clears scratch2. Its fixed-original-file bounded Σ₁
induction applies to arbitrary internal counters. The full MP runtime has a
positive internal witness; no exact binary clock or first-exit property is
asserted.

The first source check failed on missing namespace openings, a numeral/local
abbreviation simplification and deep concrete-control reduction. The original
FAIL and source/guard/log are preserved. Four narrow repairs changed no public
statement, instruction binding, import or resource limit. The repaired source
and unchanged focused audit passed 12 ordered axiom probes and 22 callers,
with only `propext`, `Classical.choice` and `Quot.sound`, and no warnings.
The source took 7.420 seconds and audit 2.779 seconds.

The guard matched 99 project prerequisites, six retained external provider
pairs and 221 inputs before and after checking. The project-import traversal
reaches five direct external boundaries; HFS.Seq is retained from parent
evidence and still rehashed. Historical inventory fields that label all six
providers as boundaries are preserved, with this distinction made explicit. It recorded the fresh source object
before the audit and verified it unchanged afterward. Its parent evidence
retains UnpairCore's original failed audit and later audit-only success without
rebuilding that source. The portable guard is byte-identical to the executed
successful guard. The ordinary maintained-default preparation queried the
compiler version and compiled no proof.

Proof commands used one thread, 4 GiB, default Lean limits and a 120-second
timeout. No dependencies, site guards or bootstrap proofs were rebuilt or
replayed. Author, root and independent reviews are retained with their exact
source, audit, repair and final-evidence scopes.

AX, the complete internal interpreter-to-Enum connection and final PA
consistency/nonhalting equivalence remain open. This result changes no machine
state count.

```sh
python Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_mp254.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --unpair-core-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-unpair-core254-verification.json \
  --output /external/fresh/mp-check
```
