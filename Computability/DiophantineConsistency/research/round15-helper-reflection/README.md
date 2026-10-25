# Affine reflection of the private common helper

This separate ordinary packet replaces d>=0 and V>=1 by the single affine
predicate v255-4>=0 on the complete original Round15 body. The inverse witness
map may reflect five private body coordinates. Every semantic power/frame port
and every other body coordinate stays fixed; this is not a fixed-whole-body
guard theorem. No new guarded layout or projected endpoint is generated.

PROOF.md proves the full affine involution and both existential directions.
The involution sends every one of the446 body residuals to itself or its
negative, so the whole body sum of squares is exactly invariant on all integer
assignments. All retained guard expressions are fixed as well. The new affine
predicate and actual row207 then supply a positive normalization of V and d,
after which fresh old Legendre triples restore the two omitted guards.

CERTIFICATE.json records every changed-coordinate occurrence, all38 old guards,
all446 row signs, the fixed complement, complete semantic inventories and both
witness schedules. check.py is standalone and standard-library-only. It imports
no incoming program, producer, optimizer or parent checker. It verifies the whole
row and sum-of-squares identities, every guard graph and auxiliary privacy,
remaining guard invariance and actual altered-artifact controls.

The initial packet contained no checker execution. Root then read the complete
final checker, proof and certificate/pin boundary, found no issue, and authorized
source-only normal/optimized replay. The commands write only external receipts;
retained author records are VERIFY.json and VERIFY_OPTIMIZED.json:

```sh
python -B check.py --output /tmp/round15-helper-reflection.json
python -B -O check.py --output /tmp/round15-helper-reflection-O.json
```

The separately sealed F-only and JOINT(F,A) theorems may be applied only AFTER
normalizing the helper and restoring d/V guards, using the matching retained
A policy. No early F-only composition with a missing A premise is licensed.
The original Legendre witness triples are private; the maps need neither their
uniqueness nor a polynomial representation choice.

SOURCE_PINS.json authenticates the exact source and complete closed ordinary
dependencies. This proposal changes no source equation, compiler, projection,
canonical page, common report, frozen parent or Lean file. It predicts no
operation, variable, degree, height or optimality improvement. The different
cap prototype retains its initial helper policy and is outside this theorem.
