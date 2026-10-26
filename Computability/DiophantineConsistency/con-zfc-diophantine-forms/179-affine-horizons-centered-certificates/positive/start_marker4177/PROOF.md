# Whole Start-marker4177 specialization of the centered inverse-trace front

## Statement, tuple, and provenance

`equation_bV.json` is the same 88-gate, exact-degree224 free-port circuit
proved in `../PROOF.md`, with exactly ten independent positive inputs.
The whole current Start-marker4177 tuple replaces the principal historical
tuple, under its own native calibration. This is a new compact front at
an upstream encoding, not an encoding invention or an identification of
old/new specialized polynomials. All four ports differ from the retained
7309 tuple; none is borrowed independently.

All four payloads use minimal unsigned **big-endian** encoding. In contrast,
the historical principal tuple is little-endian. Their full values are
reconstructed, not represented only by their hashes:

| Port | Bits | Minimal raw bytes |
|---|---:|---:|
| beta=2^196319−1 |196319|24540|
| K0 |196790|24599|
| MC |196319|24540|
| MF_source |196320|24540|

Total raw size is 98,219 bytes. The native forbidden mask is shifted by
beta exactly once: MF_source=MF_native+beta. The new byte bindings and
unmodified upstream proof/certificate/decoder are retained in `snapshot/`.

## Complete physical reconstruction, not just weighted support

The entire finite recipe and all943 indexed tiles,430 actions,436-character
seed and corrected initializer t_929=(3,436,4,4) are supplied in the pinned
radix55 page and the complete current proof. Set rho=2^47, L=4177,
B=rho^L and d=47L=196319. The full physical support is

    {0..942} union {943..951} union {973..981}
      union {992..999} union {1002..1009} union {990,991,1048}.

There are980 physical positions but only977 nonzero coefficients.
The dummies990,991 and the physical Boolean marker1048 all have weight0.
In particular1048 MUST NOT be removed when reconstructing support.
The kernel additionally has the bare monomial rho^1048, which copies
selector0, the calibrated Start. It is not a count of all selectors.
The two nonzero Start south bits1 and8 and that copied indicator recover
the full phase. Weighted-array equality alone does not prove this geometry.

`snapshot/research/start-marker-independent/PROOF.md` §3 gives every
coefficient, Phi/Psi, masks and kernel. Its verifier rebuilds all3297
coefficient slots (including the zero tail), the entire physical support,
all native masks and the new kernel. The wrapper compares every resulting
integer against its complete compressed payload and explicitly checks
marker inclusion, zero weight, and the separate Start-copy coefficient1.
The retained current certificate also rejects omission of the marker,
and checks all905 bad offsets; these finite controls do not replace the
unbounded phase/carry proof.

## Why the exact compact native interface transfers

The numerical part of `../PROOF.md` is uniform in the four ports under
the stated scalar bounds and retained parity/population assumptions.
The current native proof §4 establishes, at the new coherent tuple,

    beta odd>=31, K0>0, 0<MC<beta<MF_source<2beta,
    MC=2 mod4, MF_native=4 mod8,
    pc(MC)=196319−980, pc(MF_native)=980.

The new compact soundness proof establishes exactly X=2^R, q³|Y,
C>0, and integral nonnegative t=B_transport/(q−1), where

    B_transport=(K0+w)C−F.

The retained fixed-minus parity and half-binomial reconstruction produce
fresh source witnesses at Y(X+1)+2. The current native proof §§5–8
then decodes those actual new masks and kernel into the same calibrated
syntactic-refutation language. The decoding is independent of whether
the compact carrier used a squared trace, an unsquared trace, or the
new integer center AUEV. The scalar box alone is not this theorem.

For completeness current §§9–12 construct fresh native words for every
finite refutation, with the exact canonical outer data required by the
compact front: q a power of2, X=2^R, R=3 mod4, 3q+1<=R<q⁴,
q³|Y, and nonnegative transport quotient. Use these new words and the
new centered period-seed construction of `../PROOF.md` §4. Its exact map constructs n_new=n_old+g0V>0 at the parent's freshly
constructed positive zero, where V>0. It does not reuse historical packed
words or claim that the inverse shift preserves positivity.

## Pcs and compression boundary

Completeness requires the current kernel's Pcs, not an old Pc1/Pc0
certificate. The exact retained certificate proves the relevant primes
4177 and224113, orders23 and87, spacing2001, valuation-one lift, and
nonzero H residues9,2620,158694 modulo47,4177,224113 respectively.
`verify.py` replays this full certificate normally and under Python−O.
Its hash is b3e1368f3918e8a3371e11aed9746c2369e8770c9aaa2496b4cf797f3b85b8f8.

The frozen upstream compressed blobs remain byte-for-byte unchanged.
The upstream page's generic gzip.compress(mtime=0) full-build bytecheck
is runtime-sensitive: this runtime emits gzip OS-byte03 while the stored
header usesff. The raw mathematical integers agree. We do not claim that
upstream compressed full-build bytecheck passed. Our builder reproduces
the new graph JSON, our verifier authenticates both stored compressed
bytes and every reconstructed raw integer, and no blob is rewritten or
silently normalized. The inherited finite certify.py replay does pass.

Consequently the whole new specialized equation has a positive zero iff
there is a finite syntactic ZFC refutation at the retained ordinary
calibration. ZFC proves its absence of positive zeros equivalent to
Con(ZFC). This is not a new formal-kernel replay or a consistency decision.
