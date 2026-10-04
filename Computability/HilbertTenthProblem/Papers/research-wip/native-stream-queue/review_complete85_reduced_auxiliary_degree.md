# Independent review of the complete85 / degree155 deformation

**PASS; no correction requested.** I read the complete final author proof
and helper, the complete84 parent proof and literal source, and independently
reconstructed the new full array. The fresh reviewer authenticates the
three author files and all six pinned parent/review dependencies as inert
bytes. No frozen program was imported or executed.

| Reviewed author file | SHA-256 |
|---|---|
| complete85_reduced_auxiliary_degree.py | `2d3348d2148ad7bd9c95129bf197dbba2033f2bc735c5d2691473ca6c4aea7a1` |
| complete85_reduced_auxiliary_degree.json | `eac8cfd977ac4d932b38aa5ecdfe0d52b6adf72f52a0d63d856589f62012f8c9` |
| complete85_reduced_auxiliary_degree.md | `b86b6058d06b1c7b3c99c270146340c3166c771ea23f5366ac78d9de21532b24` |

The source reconstruction begins with the untouched84-row parent. It inserts
`auxiliary_reduced_coefficient=scaled_f_square-A` immediately before L17 and
changes only L17's coefficient operand. All83 other old definitions remain
literal. R16 remains paid and live through `norm_strong`. All seven finalizer
rows, all25 supplied ports, the six fixed numeral ports, ordinary input x
and18 positive witnesses are unchanged. Sequential topology, unique producer
names and full backward liveness pass. The actual count is **47M+38A=85**,
comprising41M+37A producers and6M+1A finalization.

The complete output expansions at eight actual exterior cuts give the old
17-term polynomial and the new31-term polynomial. These expansions include
the literal c², Delta*c², S, S², V, both factors and all finalizer products;
the proof does not replace those products by independent unpaid witnesses.
They independently establish the exact nonzero correction

    Fnew−F84=P5*Ns*(Ns−Delta)*(V²−y²).

Here P5 is proof notation, not a newly free or omitted register. The outputs
are different polynomials; the accepted semantic claim is zero equivalence.

The positive-domain argument is noncircular. Delta>0 follows directly from
the source's positive X,Y before any zero equation. Dividing the zero
equation by Delta gives an integer product containing
`Nstrong=f²−Delta*i²*c⁴` and equal to1. Thus Nstrong=±1. Since
Delta=(a+2)²−1 is0 or3 modulo4, square residues exclude−1 independently
of the auxiliary factor's sign or any native decoding. Consequently
Ns=Delta and the changed auxiliary coefficient equals S². The full parent
and child equations then agree at that same tuple. The identical argument
starting at a parent zero proves the reverse direction. Inherited universality
therefore applies on precisely the parent's valid compiler slices, with an
identity map on input and every witness.

The stronger integer-zero corollary is also correct. For nonzero Delta the
same division and modulo4 argument needs no coordinate positivity. At
Delta=0, S²=Delta²*i²*c⁴ and Ns=Delta*f²−S² vanish, so both full outputs
are zero. The reviewer checks this specialization on both fully expanded
output polynomials. There is no asserted rational or real zero equivalence,
and signed numeral assignments are not certified as compiler programs.

For the uniform degree proof, the reviewer freshly expands the full actual
prefix for all14 degree cuts, rather than accepting proposed cut degrees or
coefficient values. It then expands each complete factor at its actual cuts.
In particular the main and input a²c² terms cancel algebraically, with no
zero-set relation. The resulting seven exact factor degrees are

    22, 18, 32, 28, 7, 2, 46.

The independently obtained full leaders agree coefficient by coefficient
with all seven saved author leaders. Their product is

    32 Q0^91 h gamma0 delta² i² k0^9 w^16 s^25
       *Ttransport*T²*f⁴,

with the author's meanings of Q0,k0,gamma0,Ttransport. After expanding those
abbreviations the reviewer reproduces all120 leading terms. The distinguished
dynamic monomial has coefficient **−32 Bm1^92**, and no other fixed-numeral
coefficient term contributes to that dynamic monomial. Thus it is nonzero on
every admissible slice with Bm1>0. The final subtraction has degree12, proving
uniform exact total degree155. The separately recomputed naive gate bound
is165.

Additional fresh checks comprise two complete dense univariate executions
at different primes and assignments, all seven factor degrees and the full
leading coefficient;32 complete signed/rational source comparisons,
including all77 unaffected parent values and the output correction; and
all256 modulo4 residue cases. The diagnostics are algebraic assignments,
not valid compiler instances or full native positive-zero fixtures.

The fresh reviewer writer and normal/optimized exact replays from `/` pass:

```text
python3 /tmp/review_complete85_reduced_auxiliary_degree.py --root ABS_WIP --author-root /tmp --expect /tmp/review_complete85_reduced_auxiliary_degree.json
python3 -O /tmp/review_complete85_reduced_auxiliary_degree.py --root ABS_WIP --author-root /tmp --expect /tmp/review_complete85_reduced_auxiliary_degree.json
```

After installation, omit `--author-root` if author and dependencies share
`--root`. The reviewer uses explicit optimized-mode guards, strict JSON,
exclusive receipt creation, its own source-byte binding and type-sensitive
canonical replay. Reviewer helper SHA-256:
`15ec956cd46db3c0fcd3360eef84d81d570f29d2694a99148a10a27f1b008ac5`.
Reviewer receipt SHA-256:
`605f88b684f82cb75d1e510c366cb17b11e38c36f3e5a8c23d0727817ba0e742`.

This verifies the85/155 improvement over the previously recorded85/175
choice, with the same18 witnesses. It leaves the84-operation result intact
and makes no global optimality or exhaustive tradeoff claim.
