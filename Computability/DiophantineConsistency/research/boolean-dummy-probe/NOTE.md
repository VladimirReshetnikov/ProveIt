# A Boolean safe dummy suffices

This isolated checkpoint retains the complete length4027 geometry and K
of the frozen single-dummy tuple, and removes the second allowed bit of
the low dummy at978. The physical support still has979 positions, but
MC now clears978 bits, all physical positions other than selector1:

```
MC = beta + rho - rho^978 - G_943(rho) - Psi(rho,1).
```

The former coefficient3 of rho978 becomes1. Native core population105 is
unchanged. Padding is18 full fields4008..4025 and low27 bits at4026,
giving873 padding bits and native population978. The entire new MC and
MF_source are constructed and hashed; no former populations are reused.

Every C digit is now Boolean. A temporal binary shift by any phase1..46
leaves every digit even and below rho, so the exceptional odd spill is
absent. The temporal digit bound is rho/2. The complete Boolean convolution
maximum3829914518407087, together with the spatial unit and temporal
bound, satisfies the same global carry29 estimate. There is no extra
dummy contribution at clause predecessors; their Boolean bound is again
2M-1024. All copy fields, clauses, predecessors, phase classifications,
zero padding, and safe increments remain checked against the whole kernel.

The canonical safe subsets toggle only the low dummy bit0/1, which remains
available. The probe tests the actual whole first-cell MC mask against
dummy values0,1,2,3 and obtains exactly `[true,true,false,false]`. It also
checks the whole shifted masks at1,2,3 cells, with all dummy bits off/on:
their populations are `(d-978)N+1` and `978N+1`. Actual mask-compatible
sample integers verify both rank identities, `pc(R)=3dN+2`, and `R=3 mod4`.
These samples are controls for the universal rank algebra, not purported
native tilings or zeros of the Diophantine equation.

All935 integral phase candidates are still classified: zero,933 distinct
multiple-selector contradictions, and the exact tile942 contradiction at
offset20. The complete K, controller and source language are unchanged:
`L=4027`, `d=189269`, orders23/1342, spacing30866, lambda246929,
and `H=(18,2634,79912)`. The full four-port raw size remains94,689 bytes.
The printed MC recipe is shorter and the native proof has fewer cases;
this checkpoint makes no claim of a further raw-byte improvement.

The entire source page and decoder are authenticated before decoding.
Normal and `-O` Python runs reproduce the complete receipts. No accepted
source is changed. A separately bound complete ordinary proof, review,
and page/port binding are still required before promotion.

```
python research/boolean-dummy-probe/probe.py --write
python research/boolean-dummy-probe/probe.py
python -O research/boolean-dummy-probe/probe.py
```
