# The serial composition's aggregate bound is implied: 121 operations

The complete serial labelled-counter system in
`EXPLORATION_SERIAL_RAW_COUNTER_COMPOSITION.md` admits an exact
**121-operation** certificate: **56 multiplications and 65
additions/subtractions**, with 44 positive unknowns and 32 equations.
The fixed lower bound on its program width makes the counter aggregate
slack redundant. Its deletion preserves the positive solutions by a
unique positive-witness extension, including all Pell coordinates.

The source and receipt are
`../verification/explore_implicit_bound_serial_composition.py/.json`.
The independently checked 123-operation predecessor remains unchanged.
The relation is the same finite serial labelled computation on three
ordinary numerical counters, starting at [2x,0,0] and ending at zero,
with exact source zero tests. This note proves the arithmetic reduction;
any universal-machine compilation is a separate theorem. In particular
121 does not improve the existing universal bound of 90.

## 1. Exact source and schedule change

Delete the supplied positive unknown alpha and the single equation

    F0+F1+alpha=q+J.

Delete the two registers evaluating its sides, `bound_lhs` and
`bound_rhs`. The sum S=F0+F1 remains, since the time equation uses it.
Every other source polynomial, supplied coordinate, instruction and
free equality is unchanged. In particular retain

    q=2J+1, q=Wv, W=R^3, H(R-1)=2J,
    FKplus+FKminus=2J+H,
    G0=F0+T, G1=F1+T,
    W[(F0+F1-2J)+(FKplus-FKminus)]=(F0+F1-2J)-2x,
    2x+alphaI=R,
    6T=2(2J+H)+(R-3)(FZ-J),
    2T+alphaT=q, FZ+FZbar=2J+H,
    C+J=S_program H+TestC,
    TestV=V+Zall H,
    TestC+TestV+alphaP=q,
    NC=J+C, NV=J+V, NTC=J+TestC, NTV=J+TestV,
    R=Rmin*z_R,
    (RK-g)C+gI=(gF)q+R[V+h_s(FKplus-J)+h_z(FZ-J)].

Here S_program is the predecessor's fixed support numeral, distinguished
from the computed track sum S below. The numerals K,g,I,F,h_s,h_z,Zall and Rmin
are exactly the fixed compiled controller constants of the predecessor.
Choose Rmin>=9 in addition to its other fixed inequalities; the maintained
instance already meets this by a very large margin. Strengthening a fixed
numeral does not add an arithmetic instruction.

The packed word, its order, and its scale remain

    P6=FKplus+qG0+q^2F0+q^3G1+q^4F1+q^5FKminus,
    P=P6+q^6FZ+q^7FZbar+q^8NC+q^9NV+q^10NTC+q^11NTV,
    r=P, D0=q^12.

Keep all ten source equations of the same fixed-sign, general-scale
43-operation kernel. There are now 22 outer comparisons and 32 total.
The exact checker removes predecessor source/equality index 5 and checks
the unchanged acyclic norm correction at its new index.

## 2. Preliminary bounds without the deleted equation

All statements in this section concern ordinary integer equations;
neither power recovery nor native digit decoding has happened. Put

    S=F0+F1, A=S-2J, delta=FKplus-FKminus.

The expressions A and delta may be signed. The paid width equation gives
R>=9, hence W=R^3>=R>=9 and q>=W. The head equation gives

    0<H=2J/(R-1)<=J/4,
    0<FKplus,FKminus<3J.

The retained positive slack 2T+alphaT=q=2J+1 gives 0<T<=J. This bound
does not require any sign assumption on FZ-J. The exact time equation is

    (W-1)A=-W delta-2x.

Positivity of the flags gives -delta<=3J-2, and x>=1. Using the weaker
W>=3 for a convenient common estimate yields

    A<=[W(3J-2)-2]/(W-1)<=9J/2-4,
    S<=13J/2-4,
    F0,F1<=13J/2-5,
    G0,G1<=15J/2-5.

Thus each of the first five supplied P6 fields is less than 4q, and
FKminus<3q/2. Consequently

    q^5<P6<(3/2)q^6+4q(1+q+q^2+q^3+q^4)<2q^6.

The last gap is [q^6(q-9)+8q]/[2(q-1)]>0 for q>=9. Positivity of
every supplied field gives the strict lower bound.

The other six fields keep their original bounds independently of alpha.
The zero-flag pair is positive and has sum 2J+H<=3J. For the program,
R>2S_program+1 gives J>S_program H, so

    TestC=C+J-S_program H>C,
    TestV=V+Zall H>V.

Their retained positive aggregate slack implies TestC+TestV<=q-1=2J.
Each of C,V,TestC,TestV is therefore at most 2J-1. Adding J bounds
each native adapter NC,NV,NTC,NTV by 3J-1, as are FZ,FZbar.

It follows that

    q^11<P<2q^6+(3J-1)q^6(1+q+...+q^5)
          <3(q^12-1)/2.                         (1)

For the last inequality, substituting J=(q-1)/2 makes the difference

    [2q^11+2q^10+2q^9+2q^8+2q^7+q^6-3]/2>0.

The checker also verifies this exact rational identity and its positive
polynomial coefficients after substituting q=t+9. No bound on P6 below
q^6 is assumed or needed.

## 3. Decode just the lowest field and recover alpha

The general-scale kernel applies before digit decoding: D0=q^12>=81,
r=P>=27, r<2D0 by (1), and D0<r^2 because P>q^11. It therefore
recovers q as a power of three and D0 dividing the central binomial
coefficient at P. The enlarged direct unit-two mask theorem, in the
range (1), gives

    P<q^12,
    every ternary digit of P is one or two,
    its unit digit is two.

Every normalized q-chunk is consequently in [J,q-1]. This statement is
about P, not yet about all twelve supplied coordinates.

The first chunk is FKplus modulo q. Since 0<FKplus<3J<2q, a carry
from this field could only mean FKplus>=q. Its remainder would then be
at most 3J-1-q=J-2, below the smallest native chunk. Therefore

    FKplus=P mod q>=J.

Only this one field has been identified. The sign-pair equation now gives

    delta=2(FKplus-J)-H>=-H.

Substitute into the exact time equation, retaining x>0:

    A<WH/(W-1)
      =[W/(W-1)]*[2J/(R-1)]
      <=(9/8)*(J/4)=9J/32<J.                   (2)

This bounds the actual computed A=F0+F1-2J, even if an individual
F_i-J has not yet been shown nonnegative. It uses neither complete
three-block banks, native program fields, nor the source zero tests.

Define

    alpha=q+J-S=J+1-A.

It is a positive integer by (2), and it satisfies the deleted equation.
Every new positive solution has therefore been extended to an old
123-operation solution with exactly the same remaining coordinates.

Conversely, forgetting alpha from any old positive solution satisfies
every new equation. Its value in an extension is uniquely determined
by the displayed formula. The two maps are inverse. This proves an
exact positive-witness bijection, rather than merely equality of the
represented endpoint predicates.

All of the predecessor's subsequent conclusions now apply: every supplied
field is decoded, the serial controller is a permitted labelled path,
its typed signs and zero tests match the raw counters, parity forces
complete three-register banks, and the even-index positive Pell converse
is available. No extra Pell witnesses are reconstructed in the bijection.
The general six-field overflow and weak-field recovery lemmas are valid
related results, but the stronger paid program width makes them
unnecessary in this proof.

## 4. Accounting and evidence

The deletion removes exactly two additions, one positive unknown, and
one source equation. Products and the raw-input operation x+x are
unchanged. Thus

    123-2=121=56M+65A,
    45-1=44 positive unknowns, 33-1=32 equations.

The checker expands every retained source equality against the complete
121-instruction schedule, including the inherited norm correction. It
checks the full-word upper bound symbolically. It also repeats both
complete canonical serial paths of the predecessor, for x=1 and x=2.
They satisfy the stronger old bound, so deleting alpha leaves all
22 retained outer comparisons true. Their full packed words and exact
central-binomial valuations remain unchanged: 209,952 and 314,928,
respectively. All twelve fields and the positive-kernel extension
hypotheses are checked; the enormous Pell coordinates themselves are
not instantiated.

These numerical examples corroborate the complete proof and do not
constitute an exhaustive search over malformed joint assignments.
The complementary sign and zero flag fields remain supplied and masked.
Removing either pair, merging other bounds, or applying an independent
universal-program compiler requires a separate maintained result.
