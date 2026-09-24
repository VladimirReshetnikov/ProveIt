# The merged program word admits a full false positive for an empty graph

The proposed replacement of the four separate program masks by
`UH-F,F`, with F=C+V, is unsound for the complete raw-counter interface.
This note applies `EXPLORATION_MODULAR_FILL_MERGED_WORD.md` to an actual
fixed Sidon controller that accepts no positive input. The constructed
positive solution has ordinary input x=1. It retains both sign masks,
both zero-event masks, all counter guards, the paid width and input
bounds, the time equation, and the complete positive43-operation Pell
block at scale q^10.

This is a counterexample to the proposed merged-word source system.
It is not a counterexample to the complete101 or102 constructions,
which retain separate state and junk masks. The proposed99 arithmetic
ledger is not promoted as a universal bound.

## 1. An actual empty controller and a separated combined support

Use the eighteen-state fixed graph and Sidon construction in
`EXPLORATION_ROM_ZERO_MASK_OMISSION.md`. Its edges are i to i+1 for
0<=i<17, together with17 to12 and17 to0. Its first six signs are
+++---, restoring the bank[2x,0,0]. State6 then requests that register0
be zero. Every positive first return passes that state. Therefore the
fixed graph accepts no x>0; this statement does not depend on the
subsequent numerical cleanup.

Keep its state and flag coordinates and spacing ell=3, with3^ell>18.
Multiply K,g,hs,hz together by3^2166. This shifts only the fixed output
band, preserves the graph and all row identities, and makes the least
exponent of K equal2508, greater than every state exponent. Let c_i
be the fixed singleton of state i and I=c_0. For every legal edge i to j,
form its correct combined row

    f_ij=(K+1)c_i-g c_j-hs*plus_i-hz*nozero_i.

Every such row is Boolean and positive. Its positions below2508 consist
exactly of c_i; all correct junk is above the state positions. Define U
as the union of these nineteen correct row supports. It has807 occupied
positions, all on the spacing-three grid. Choose the optional column
c=I, which occurs in U, and put B=U-c>0.

The companion checks the following strict fixed-numeral inequality:

    (K-1)(U-c)>hs+hz+gI.                                  (1)

Its positive margin has24,369 binary digits. This is an exact integer
comparison, not a floating-point estimate.

Choose a fixed on-grid threshold Zon=3^8943, above2U, (K+g)(S+1),
g(I+1), hs+hz and81. Take R=3^8946 and B0=27. The positive width
coordinate

    z=(R-1)/(B0-1)-Zon

satisfies the retained paid equation `(B0-1)(Zon+z)=R-1`.
All correct fixed row products fit inside R, R>2U, and R is divisible
by g. These large fixed constants do not introduce variable exponent
operations into the proposed source; they specify the counterexample's
choice of witnesses and fixed compilation numerals.

Put T=R/g and d=(K+1)T-1. Then d>1 and gcd(d,R)=1. From(1),

    (TK-1)(U-c)>T(hs+hz)+I(R-1).                            (2)

Indeed TK-1>=T(K-1), and I(R-1)<TgI. This is precisely the positive
C,V condition of the modular-filling lemma. The checker's actual
modulus has16,433 binary digits. No factorization or materialization of
its multiplicative order is needed in the proof.

## 2. A real numerical trace with fixed input one

Start the three raw registers at[2,0,0], representing x=1. Use the
twelve serial signs

    +++--- -++---,

with phases cycling0,1,2. These reach[0,0,0]. Append n copies of
+++---, each preserving the all-zero bank. Declare the sole true zero
request at row1, where register1 is zero. This annotation is a genuine
numerical zero test. Both sign words and both complementary zero words
are positive.

Let L be the multiplicative order of R^6 modulo d and take n=dL.
The total duration is u=12+6n, so q=R^u, W=R^3 and v=q/W are positive
integers. Set J=(q-1)/2 and H=(q-1)/(R-1). Split every source value into
two Boolean ternary tracks A0,A1, as in the proved raw-counter interface.
The largest source value is three, independent of n. The initial value
two forces both track words to be positive. With Z=R and D=H-Z, set

    t=(R-3)D/6.

Both t-A0 and t-A1 are Boolean and nonnegative: every nozero row
contains the full lower-row interval in t, while the sole true-zero
row has both tracks zero. All eight counter fields

    Kplus,Kminus,Z,D,t-A0,A0,t-A1,A1

are Boolean. Every supplied counter coordinate is strictly positive.
The exact telescoping time equation is

    W(A0+A1+Kplus-Kminus)=A0+A1-2.

Set alphaI=R-2>0. This gives the paid raw-input equation with x=1.
Appending neutral loops changes neither the endpoint nor the ordinary
input. The counter trace is not asserted to follow the intended empty
controller; the forthcoming merged route is exactly what incorrectly
admits it.

## 3. Fill the merged word while preserving all counter fields

Apply the general modular lemma with prefix length12, loop length6,
and B=U-c. Begin with Fbase=B H. At the d row positions

    b_j=12+6Lj,    0<=j<d,

there is an independent optional digit c. Each lies inside the trace,
and all are absent from Fbase. Their effects on

    N(F)=T(F+hs*Kplus+hz*D)+I(q-1)

are the same unit `w=T c R^12 mod d`. Choose0<=M<d with
`Mw=-N(Fbase) mod d`, and add c at the first M optional positions.
The resulting F and UH-F remain Boolean, and d divides N(F).

Define C=N(F)/d and V=F-C. Condition(2) proves

    0<C<F<q,    V>0.

Multiplying dC=N(F) by g proves exactly the original route

    (RK-g)C=gI(q-1)+R(V+hs*Kplus+hz*D),
    F=C+V.

Thus the procedure changes only F,C,V. Every genuine numerical counter
mask, flag pair, zero test, geometry equation and input/time equation
from Section2 stays unchanged. The fixed program word has not supplied
a valid path: it has supplied only a divisible scalar equation after
its separate support masks were removed.

## 4. Complete positive packed-index and Pell extension

Pack the ten fields

    Kplus,Kminus,Z,D,t-A0,A0,t-A1,A1,UH-F,F

in base q as P. All are Boolean and less than q. Its unit digit is one,
because the first sign is plus. Put

    D0=q^10,   r=P+(D0-1)/2,   beta=D0-r.

Then beta>0, r has ternary digits one or two with unit digit two, and
the direct ternary carry theorem gives

    v_3 binom(2r,r)=10mu.

The sum of the ten fields is2H+2t+UH. Since u is even, H is even,
so P is even. Also `(q^10-1)/2` is even, giving even r. The inequalities
D0>=81, r>=27, r<D0<r^2 hold with a wide margin. The complete positive
fixed-sign43-operation Pell converse therefore supplies every remaining
positive auxiliary at this actual scale D0. It requires these numerical
index conditions, not correctness of a purported program interpretation.

This satisfies all thirteen outer equations of the proposed merged
source and its ten retained Pell equations with x=1. In the packed
outer equation use D0=q^10 and the ten-field P above; F is the computed
sum C+V, and the retained width coordinate is the positive z from
Section1. The fixed graph accepts no positive input, so this is a full
false positive for that proposed source system.

## 5. Evidence boundary

The source-interface checker is
`../verification/explore_merged_program_empty_graph.py`, with its
adjacent receipt. It checks the actual eighteen-state/nineteen-edge
Sidon constants, all correct merged rows and their807-position union,
the paid width, the strict positivity margin, and coprimality of the
optional-digit coefficient. It runs complete genuine numerical
templates with0,1 and2 neutral loops at the actual width:12,18 and24
rows, checking all eight counter masks and the exact time equation.

The generic modular lemma has a separately materialized toy regression.
Here the actual order L, the resulting enormous repeated word, and the
Pell auxiliaries are supplied by the constructive proofs rather than
numerically instantiated. No finite regression is substituted for that
existence argument. The companion does not claim a newly verified
99-instruction schedule; the mathematical source system itself is
refuted, so the proposed operation reduction is unusable regardless.
