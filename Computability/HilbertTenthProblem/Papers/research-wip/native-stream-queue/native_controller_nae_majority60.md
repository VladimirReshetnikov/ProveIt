# The same even-length NAE relation in 60 operations

This source proves exactly the even-length projection of
[NAE61](native_controller_nae_majority61.md), using **60=33M+27A**,
18 equations and 25 strictly positive auxiliaries beyond the same five
positive parameters q,F0,F1,R0,R1. A single packed-word bound replaces
the two individual field bounds. The positive-port gate excludes the
low-field carry that this replacement would otherwise permit.

The exact semantics remain q=3^t for even t>=2, H=(q-1)/2,
F0=H+D,F1=H+V for Boolean ternary words D,V with D's units digit 1,
R0=3^a,R1=3^b for 1<=a,b<=t, and

    d_j+(rot_a d)_j+(rot_b d)_j=1+v_j at every position.

Thus V is the majority of three bits that are not all equal. Zero V
and identity rotations are allowed. There is no ordinary-input or
acceptance compiler; the established complete universal bound remains76.

## 1. Source change and exact count

Keep the q^2-scale kernel, gate and rotation equations of61. Replace

    F0+alpha0=q, F1+alpha1=q

by the single equation

    r+alpha=q^2,                                      (1)

with positive alpha. The scale q^2 is already computed. The six outer
instructions are now

    twice_H=H+H; q_calc=twice_H+1;
    p0=q*F1; P=F0+p0; D0=q*q; packed_bound=r+alpha.

Their three comparisons are q=q_calc, r=P and packed_bound=D0. They
cost 2M+4A; adding the retained43 and the same eleven routing/gate
operations gives60=33M+27A. There are18 comparisons and25 positive
auxiliaries, hence30 positive coordinates including the parameters.
The [source](native_controller_nae_majority60.py) imports frozen61,
audits the literal schedule and all18 polynomial residuals, and checks
the shifted auxiliary-norm correction at its new equation index.

## 2. Pre-power bounds and recovery of the actual fields

The new bound and positivity give

    q=2H+1>=3, q+1<=r=F0+qF1<q^2,
    1<=F1<=q-1.

The unchanged positive gate is

    F0+A+B=F1+H.

Consequently

    F0<=F1+H-2<=q+H-3<2q.                             (2)

This bound is obtained before digit typing. If q=3, then H=1 and
(2) gives F0<=F1-1<=1, forcing F0=1,F1=2,A=B=1. The transport of A
then says R0=2K0, impossible because R0 divides3. Thus q>=5.

The actual index and scale therefore satisfy exactly the61 preliminary
bounds: D0=q^2>=25, r>=6, D0<r^2 and 6r/a<6/(D0+1)<1/2.
Its unchanged kernel proof recovers q=3^t, q^2 dividing binom(2r,r)
and even r from the generic signed positive-branch theorem. None of
those arguments uses separate bounds on F0 or F1.

Since r<q^2, the maximal 2t doubling carries make its two actual
normalized q-chunks native, with low chunk G0 having units trit2.
In particular

    G0>=H+1.                                         (3)

If F0>=q, (2) and F0<2q would instead give

    G0=F0-q<=H-3,

contradicting (3). Hence F0<q. We already know F1<q, so both supplied
fields are precisely the actual native chunks. The61 proof now
recovers Boolean D,V, the typed rotations, the coefficientwise gate,
and even t without change.

For clarity, the packed bound alone does not imply native supplied
fields. At q=9,H=4,F0=14,F1=4, the value P=50 is below81, has even
parity and the required four ternary doubling carries, yet F0>=q.
This tuple fails the positive-port gate, which would require A+B=-6.
It is not a counterexample to the complete60 source. It explains why
the bound saving is valid for this composition and is not a standalone
two-field typing improvement.

## 3. Converse, examples and evidence

For every semantic point, the61 converse already has r=F0+qF1<q^2.
Set alpha=q^2-r>0 and discard its two individual field slacks. All
other source equations and positive witnesses are unchanged. Conversely
Section2 derives the omitted bounds, so alpha0=q-F0 and alpha1=q-F1
would be positive. This also proves direct equivalence of the60 and61
projections, rather than only soundness of the cheaper source.

The t=2 examples have q=9,H=4,F0=5. With F1=7 and a=b=1, the packed
index is r=68 and alpha=13. With F1=5,a=2,b=1, it is r=50 and
alpha=31. Both have complete positive kernel extensions. The zero-V
example at t=6 is retained as well.

The [receipt](native_controller_nae_majority60.json) checks the new
pre-power inequalities on arbitrary positive fields satisfying the gate's
derived bound, then exhausts valuation/typing equivalence through t=5,
including candidate low-field carries. Every admitted even-length NAE
word through t=8 is lifted to the new literal positive outer source.
The full polynomial schedule is rechecked, while the unchanged Pell
and parity implications are inherited from the reviewed61 proof.

Run `python native_controller_nae_majority60.py` for a fresh comparison
with the saved receipt. The conditional rotation-closure spectral lemma
in61 Section7 applies unchanged. No larger computational conclusion
follows from this operation saving. Two independent complete proof/source
reviews and fresh default-receipt replays passed with no findings.
