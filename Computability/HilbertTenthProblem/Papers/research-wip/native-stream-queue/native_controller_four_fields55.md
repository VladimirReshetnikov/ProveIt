# Four independent native fields in 55 operations

The retained plus-sign Pell equations themselves force an even packed
index. Removing the redundant explicit parity instruction from the
[frozen56/58 component](native_controller_four_fields56.md) therefore
gives complete **55=30M+25A** and **57=30M+27A** typing relations.
The earlier source and receipt are preserved unchanged.

The positive parameter projection is exactly the same: q=3^t for some
t>=1; F0,F1,F2,F3 each have t native trits in{1,2}; F0's units trit
is2; and the sum of the four fields is even. The57 variant additionally
supplies the positive repunit H=(q-1)/2 and computes2H. These are four
independent Boolean planes after subtracting H, subject to the explicit
origin condition and the proved global parity condition. They are not a
universal computation certificate; the complete universal bound stays76.

## 1. Exact deletion and why it preserves the projection

Keep the four positive slack equations Fi+alpha_i=q, the packing
r=F0+qF1+q^2F2+q^3F3, the scale D0=q^4, and all ten retained kernel
equations. Delete only the supplied positive coordinate nu, the computed
product even_r=2nu, and the comparison r=even_r.

The pre-power analysis in the56 proof does not use that comparison:

    q>=2, D0>=16, r>=15, r<D0, D0<r^2,
    6r/a<6/(D0+1)<=6/17<1/2,
    p>=r+2>=17, c=psi_A(p)>AD^2, A=a+3, D=A^2-1.

It therefore recovers the same main and auxiliary facts before assuming
parity:

    p=2r+1, c=psi_A(p), f=chi_A(m), c divides m,
    m>=c>2p, R=ic^2=D*psi_A(m)>1.

Pell growth also gives

    f>=chi_A(2p)=1+2D*c^2>2c.

Put u=2r+1+jc=c+of. It is positive and satisfies

    R^2*(u^2-y_aux^2)=1-y_aux^2,
    u=p modulo c, u=c modulo f,
    c divides R, R^2=D(f^2-1).

These are all hypotheses of the generic **plus-sign** case in Section4
of [the signed-parity theorem](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md).
That theorem is stated for every A>=2 and allows arbitrary auxiliary
indices; it is not restricted to its document's fixed-minus application
at A=a+2. It gives (-1)^((p-1)/2)=1, so r is even.

Thus every positive55/57 solution extends to the frozen56/58 source
by choosing nu=r/2>0. Conversely every56/58 solution restricts to the
new source by forgetting nu. This proves exact equivalence of their
positive parameter projections and inherits both the complete typing
theorem and every positive converse coordinate. No parity assumption
is inferred from canonical witnesses alone.

## 2. Exact counts and checks

The [new source audit](native_controller_four_fields55.py) imports the
unchanged frozen source, removes exactly that multiplication and comparison,
and independently checks all resulting polynomial residuals and the
inherited acyclic auxiliary-norm correction.

| Relation | Multiplications | Additions/subtractions | Total | Equations | Positive auxiliaries |
|---|---:|---:|---:|---:|---:|
| Four independent fields |30|25|55|15|21|
| Four fields with supplied H |30|27|57|16|22|

Both have the same five positive parameters q,F0,F1,F2,F3. All retained
supplied coordinates occur in the source. The
[saved receipt](native_controller_four_fields55.json) replays the bounded
pre-power and field-typing domains from the frozen checker. Those finite
tests support the unchanged digit argument; implicit parity is established
by the signed theorem and the hypothesis audit above, not by testing only
even examples.

Independent mathematical/source review and fresh default-receipt replay
passed, including every hypothesis of the signed-parity bridge.

No finite controller, shifted incidence, ordinary numerical input or
acceptance condition is included in55 or57. This refinement removes a
redundant parity operation from a reusable typing interface only.
