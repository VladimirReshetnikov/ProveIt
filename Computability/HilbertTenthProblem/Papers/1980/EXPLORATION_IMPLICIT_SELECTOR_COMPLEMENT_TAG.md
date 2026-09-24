# Recovering the selector complement from the first mask blocks

Review status: author verification and independent root and binary complete
proof/source reviews and fresh runs passed without findings. Mathematical
construction and arithmetic are frozen.

This separate successor to `EXPLORATION_POSITIVE_CONTENT_SUM_TAG.md` costs
**113 operations=55 multiplications+58 additions/subtractions**, with
**37 positive existential unknowns and24 equations**. It preserves the
complete positive encoded-binary-word halting equivalence of114. The
specified input contract, fixed binary tag program and external raw-input
limitations are unchanged. This is not a universal numerical-input bound.

## 1. Exact arithmetic change

Delete the positive supplied coordinate F_S0, its adapter S0=F_S0-1,
and the comparison computed by headsum=S0+S1 against H. Instead compute

    S0=H-S1.                                               (1)

This removes two additions/subtractions and adds one. There is one fewer
positive coordinate and one fewer equation. All other instructions and
comparisons are unchanged. In particular the field order remains

    Gstar,Q,S0,S1,M0,M1,E,Ebar,Nbar,N,

where Gstar=Q+AH+S0 and Nbar=Nsum-N. The same18-operation Horner packing
is used. S0 and Gstar can now be negative before decoding; this fact is
included explicitly in the proof rather than treated as a supplied domain.

## 2. Bounds and a positive packed value before the kernel

The unchanged initial, length and containment equations give exactly the
pre-power bounds from114:

    R=CA>K^2, q>=R, H=(q-1)/(R-1)>0,
    L<K^2*q/(3R-K)<q/2, Nsum<L/2<q/4.

The nonnegative marker coordinates satisfy M0,M1<q/2. From
2Q+S1=M1, both Q<q/4 and S1<q/2 follow without using a head mask.
Therefore the signed coordinates satisfy

    -q/2<S0=H-S1<=H<q,
    -q/2<Gstar=Q+AH+H-S1<q/4+q/3<q.                       (2)

The upper guard bound uses the same (A+1)H<q/3 inequality as115.
The retained prefix equation and nonnegative E,Ebar still give
E,Ebar<=cH<q. Thus, among the first eight fields, only positions0 and2
(Gstar and S0) can be negative. All eight are strictly less than q.

Let Plo be their formal packing. From(2) and nonnegativity of the other
six fields,

    Plo>-(q+q^3)/2>-q^3,   Plo<q^8.                       (3)

The highest pair is still

    T=Nsum+(q-1)N>=1,
    P=Plo+q^8 T>q^8-q^3>0.                               (4)

Here N=F_N-1>=0 and Nsum is a supplied positive coordinate. Equation(4)
restores the positivity needed for the unchanged kernel bootstrap even
though Plo itself might be negative.

With D0=q^10, 2r+1=D0+2P and r+betaP=D0, the same inequalities give
D0>=81,r>=27,r<2D0,D0<r^2. The generic44-operation kernel therefore
proves q and R are powers of three, q=R^t, and P is a Boolean ternary
word with unit trit1. No sign of S0 or Gstar is assumed during this step.

## 3. Decoding the low blocks removes both possible negative values

Let J=(q-1)/2, a proof abbreviation only. The integer Gstar lies in
(-q/2,q). All other terms in the packing are multiples of q. If Gstar
were negative, the lowest q-chunk of P would be q+Gstar>q/2>J,
which a Boolean ternary word below q cannot attain. Hence Gstar>=0,
and it is precisely P's first Boolean block.

The next field Q is nonnegative and less than q, so it is precisely the
next Boolean block with no carry or borrow. At position2 the same argument
applies to S0: by(2), a negative value would give the normalized chunk
q+S0>q/2>J. Thus S0>=0 and it too is Boolean.

All of Plo's fields are now nonnegative and less than q. In particular
0<=Plo<q^8, so the proof for the highest pair in114 applies unchanged.
The upper bound P<=(q^10-1)/2 gives T<=(q^2-1)/2 and N<=J. A negative
Nbar=Nsum-N would have a low chunk q+Nbar>J and is impossible. Thus Nbar
is nonnegative, both highest fields have their original Boolean meanings,
and all ten field masks are recovered.

Identity(1) restores the head equation S0+S1=H. The earlier Gstar proof
therefore restores the original guard and the full31 tag interface. The
same first-halt theorem proves soundness under the specified encoded-input
contract, including possible rows after the first genuine halt.

## 4. Unique positive extension and unchanged Pell witnesses

Every new solution has the unique positive former coordinate

    F_S0=S0+1>0.

It satisfies the deleted adapter and head comparison. Every retained
coordinate and register has exactly its old114 value. In particular the
packing order, packed word P, r, betaP and all seventeen Pell auxiliaries
are unchanged. Conversely, the114 head equation makes S0=H-S1, so deleting
F_S0 from an old solution gives a new solution.

This is an exact solution correspondence with a unique positive-coordinate
extension. Unlike the preceding packing-order change, it does not require
new Pell witnesses. Possible zero values of S0 are preserved: F_S0 is then
one. The canonical checks contain100 such histories.

## 5. Fresh source and numerical evidence

`../verification/explore_implicit_selector_complement_tag.py` constructs
the complete113-instruction DAG. It independently expands all13 outer
sources and11 kernel sources, including the retained norm-source correction
at combined index21. Under the formal substitution

    F_S0=H-F_S1+2,

the removed head source is identically zero and every surviving polynomial
and the packed index match114 exactly. The counterexample possibility
before typing is addressed by the proof, not hidden by that formal map.

The bounded low-field regression covers66,420 signed coefficient pairs.
It rejects49,634 cases with a negative field:33,030 at the first block
and16,604 at the selector-complement block. These are normalization tests
on the stated coefficient ranges, not asserted full tag source solutions.

Fresh canonical construction checks944 halts and2,318 source rows,
evaluating all13 new and14 restored old outer comparisons. All944 packed
indices remain identical;598 are even and346 odd. All ten fields and
the exact native valuations are checked. The three-formal-row example
with a true halt after one step is retained. The428 cutoff runs remain
unclassified. Enormous Pell auxiliaries remain justified by the general
kernel converse and exact preservation, without materializing their values.

No published predecessor, ordinary input encoding, universal startup or
universal operation frontier is changed by this result.
