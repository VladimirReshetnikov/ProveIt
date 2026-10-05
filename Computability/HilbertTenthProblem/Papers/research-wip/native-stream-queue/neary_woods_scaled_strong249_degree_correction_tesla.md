# Corrected degree bounds for the unchanged249 U9 sources

The geometry-only249 source has the corrected total-degree upper bound
**936**. Joint-only remains **1038** and both-core becomes **1048**.
All six emitted arrays, the **249=129M+120A** ledgers,43 positive witnesses,
unconditional multiplier positivity and identical complete positive zero
sets remain unchanged. These are upper bounds, not exact total degrees.

Aristotle found a degree-counting error during independent review of the
frozen author packet. The original trio is preserved unchanged. This
separate correction supersedes its geometry degree assertions and the
corresponding manual-degree metadata; it does not alter or evaluate any
source array. Root and Tesla independently confirmed that the parent926
bound remains valid.

## 1. Numbered retention of the errors

**Correction remark 1 (the geometry odd multiplier has positive degree).**
The original Section4 asserted `deg Yg<=1`, `deg ag<=4` and
`deg Delta_g<=8`. These claims are false under its own convention that
every supplied witness has degree1. The literal geometry definition is

    Yg=(2*geo__odd_half+1)*Q.

Both `geo__odd_half` and the positive-scale polynomial Q have degree1.
Thus Yg has degree2, Xg has degree3, ag=Yg(Xg+1) has degree5, and
Delta_g=ag^2+4ag+3 has degree10.

Here is explicit nonzero leading-term counterevidence, not a numerical
source execution. Let ell be the degree-one part of `load__r`, let
`d0=repunit_divisor>0`, `r0=recoder_radix>0`,
`o=geo__odd_half`, and `j=duration_quotient`. Reading the retained loader
formulas gives

    Q_top=d0*ell,
    (duration_J)_top=r0*d0*ell*j,
    (Xg)_top=r0*d0^3*ell^2*j,
    (Yg)_top=2*d0*o*ell,
    (ag)_top=2*r0*d0^4*o*ell^3*j,
    (Delta_g)_top=4*r0^2*d0^8*o^2*ell^6*j^2.      (1)

The final polynomial in(1) is nonzero and has degree10, directly
refuting the recorded discriminant bound8. This works for both program
interfaces. On a fixed-program slice ell still has a nonzero variable
part, so the correction is not removed by fixing the program parameters.

**Correction remark 2 (reported scaling bounds and metadata).**
The original headline/table reported geometry934 and both1046, and its
helper used8 for the geometry scaling increment. Those bounds are not
supported by its `926+deg multiplier` argument. The corrected increments
are10,112,122, giving936,1038,1048. This correction does not claim that
the actual full degrees exceed934 or1046; no such exact-degree theorem
was proved. It retracts those unsupported upper-bound derivations and
replaces them by the valid larger upper bounds below. The original
receipt's six `manual_degree_upper_bound` fields must be read with this
correction; a successful replay of that frozen helper would reproduce
the old metadata, not repair its mathematical mistake.

## 2. The parent926 bound remains valid

The corrected geometry cut degrees are

    deg Xg=3, deg Yg=2, deg E=5, deg ag=5,
    deg Delta_g=10, deg k=1, deg c=3.

Put H=4ag+3 and D0=Xg+ga*H, so `deg H<=5`, `deg D0<=6`.
The actual main norm has the all-ring cancellation

    (ag*c+D0)^2-(ag^2+H)c^2
      =D0^2+2ag*c*D0-H*c^2.

Its degree is therefore at most14. The auxiliary coefficient has degree
at most `2*10+2+4*3=34`; since V=of-c has degree at most3, its complete
auxiliary norm has degree at most40. The first norm's non-square term
is a constant multiple of `E*(kYg)*signed_gap`, of degree at most9.
The normalized strong norm has degree at most `10+2+4*3=24`.
Both index and coupled-linear factors have degree at most6. Thus the
six unchanged geometry factors retain precisely the parent's bounds

    14,40,9,24,6,6, with sum99.

The four remaining outer factors retain bounds4,2,2,3, with sum11.
The six joint factors retain bounds129,322,73,178,57,57, with sum816.
Consequently the parent's product-minus-one bound is still

    99+11+816=926.                                (2)

This manual verification uses the actual factor formulas and their
genuine main-norm cancellation, not an on-zero simplification or degree
propagation through a saved array.

## 3. Corrected complete bounds and unchanged semantics

The frozen coefficient-sharing proof gives exact complete identities

    F_geo=Delta_g*F250,
    F_joint=Delta_j*F250,
    F_both=Delta_g*Delta_j*F250.

The joint discriminant bound112 is unchanged. Combining these identities
with(1)--(2) gives, for each of the two program interfaces,

| Scaled cores | Operations | M | A | Positive witnesses | Degree upper bound |
|---|---:|---:|---:|---:|---:|
| Geometry |249|129|120|43|936|
| Joint |249|129|120|43|1038|
| Both |249|129|120|43|1048|

The geometry-only variant still has the best proved degree bound among
these three equal-cost variants. The original positive-prefix proof
establishes both discriminants strictly positive before any equation;
the identity map still gives equality of every complete positive zero
tuple. No input loader, valid program hypothesis, witness domain,
history quantifier, operation count or source row changes. The separate
universal84 bound is unchanged.

## 4. Preserved artifacts and correction scope

The unchanged original author trio is

| File | SHA256 |
|---|---|
| `neary_woods_scaled_strong249_tesla.md` | `2230f44faee7e2ecebb0ce29722462f121a49e85addf3740d8b8b54efd7bc8a4` |
| `neary_woods_scaled_strong249_tesla.py` | `ba382dda0e52d6821a5808a3dcc92fb45c4e8bbf0b5e1c2510b9b607ccea21ad` |
| `neary_woods_scaled_strong249_tesla.json` | `e8fb322a18ec77cf9936ebb7d9e25d86414b66f8db561c4a64edb2ef16aba35c` |

Its parent250 MD and JSON remain pinned at
`1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330`
and `d2f1ae7870cb8ec295d4401a8e9c951047f0e92cf2b6e6f4bb723c6b483f1ebf`.
The companion correction JSON binds these original bytes, the six exact
unchanged source hashes and the corrected field values. It is a metadata
override record, not a replacement arithmetic source or fresh compiler.

Only fresh byte/hash/JSON metadata handling accompanies this correction.
No frozen helper was replayed or imported, and no source array was
evaluated. No new scientific finite test or exact-degree claim is made.
No repository or Git mutation occurred. Independent review of the
corrected bundle is recorded separately.
