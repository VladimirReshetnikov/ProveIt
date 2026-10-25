# Normalized common remainders and an odd-square radix

## The literal composition

The parent in `parent252/equation/equation.json` is the 252-integer,
182-residual common-remainder quartic delivered in
`ConZFC_Common_Remainders_Radix47_2026-10-25.zip`, at ProveIt commit
`3ecd6a6cf53d47519228328567f45fb7ee9781d9`. The odd-square lemma is inherited
from the concurrently delivered Centered Residues package, copied verbatim
as `ODD_SQUARE_SOURCE_PROOF.md`. Neither underlying idea is claimed new here.
Their composition was absent from the eight inspected current archives.

In the parent's zero-based coordinate list, B=x_5 and the actual radix is
q=x_107-1. Its output guard (row179) is

    q-B-1 = a^2+b^2+c(c+1),

where (a,b,c)=(x_243,x_244,x_245). These three coordinates occur in that row
only. Delete this row and these coordinates. Keep every other coordinate in
order and add a new final integer coordinate z. Add the row

    q-(2z+1)^2 = 0.

Thus the literal translated row is x'_107-2-4z-4z^2=0, not
x'_107-1-4z-4z^2=0. This translation is independently checked.
The single equation is the sum of squares of the resulting 182 residuals.
It has 250 unrestricted integer coordinates, degree4, 5324 collected
monomials and coefficient height128446.

## Soundness without a circular radix assumption

The signed frame, squared semantic anchor and pooled orientation argument
retained in the parent use squares of proposed power atoms. They do not
require the deleted q>=B+1 premise. They orient the principal Pell pairs at
signed requested indices, including the known positive cofinal horizon
t>=16. Its power request at base F^2+1 gives V=(F^2+1)^t, also when F=0
because the retained base-one lemma applies.

The two retained factorial guards give B>=1 and BF=V+s, s>=0.
Consequently F>=1, B>F, B>=2 and y=V(V-1)>F+2. Interpret N=B^x next.
Its base is now at least2. The inherited negative-index exclusion forces
x>=0. The first beta endpoint excludes a negative initial quotient and
gives x>=F+1>=2; the final endpoint gives x>=2+(t+1)y.

The new odd-square equation gives q>=1, so q+1>=2. The nine actual CRT
representatives, and the derived label, are exponents of requests at base
q+1; the same signed-index lemma makes them nonnegative. Thus
H=1+sum of the nine representatives is at least1. Finally interpret the
request q=(BH)^x. Its base is at least2, and x>=2. It follows that
q>=B^2>B, so the omitted output slack q-B-1 is nonnegative. The universal
ternary representation of nonnegative integers supplies fresh a,b,c for
the deleted row.

Every other final row is unchanged. In particular the three normalization
ratios, eleven normalized digit rows, common M=q^x remainder norm, Horn
rows and all intermediate-variable equations are unchanged. Therefore a
zero of the new equation extends to a zero of the published252 parent.
Its retained exact inverse projections give its arithmetic certificate,
and its proved common-remainder and C222 calibration recover a finite ZFC
refutation. No coefficient margin is reused before its original premises
have been restored.

## Constructive completeness

Start with a finite C222 refutation. The retained cofinal construction
chooses t=16+h^2, F=t!, V=(F^2+1)^t and y=V(V-1). Since y is even, every
beta denominator, including the two endpoint moduli, is odd. The valid beta
codes x form a CRT class of odd period. Choose an arbitrarily large even
x in this class, preserving every required threshold.

Each reciprocal CRT factor 1+F^2/i is odd: F^2/i=F(F/i), and F is even.
Thus B and N^2=B^(2x) are odd. Changing a representative by N^2 preserves
all its required congruences while reversing its parity. Choose the same
dominant representative a in [2N^2,4N^2), and b of opposite parity. The
retained constructor identities give the semantic label h>=2a^2 and
h=1+a+b modulo2, so the label is even and dominates the other indices.
Choose a third independent representative's parity so the sum of all nine
representatives is even; it can remain in (0,2N^2]. This preserves the
dominance and every precision bound and makes H odd.

Now q=(BH)^x is the square of the odd integer W=(BH)^(x/2). Set
z=(W-1)/2. The retained canonical private Pell and source witnesses
exist by the parent's constructive proof. Its normalized remainder
witnesses are R_i=(M/L_i)r_i^0 with R_i<M/32. The single norm gap has
its old ternary representation. Hence all the retained rows and the new
odd-square row hold, producing an integer zero of the new equation.

## Calibration and status

Both directions are ordinary finite arithmetic proofs formalizable in ZFC,
composed with the unchanged named interfaces
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Therefore ZFC proves
that the new polynomial has no integer zero if and only if Con(ZFC).
This is an exact composition of two existing mechanisms, with an improved
explicit endpoint. It is not a new logical encoding, a global minimum,
a consistency proof, or a new end-to-end proof-assistant development.

The retained source, transformation certificates and proof closure are in
`parent252/`; its upstream source licenses are retained. `build.py`
reconstructs all new coefficient files. `verify.py`, which does not import
the builder, verifies the complete coordinate deletion, translated new
row, retained residual list, collected quartic and measured metrics, with
five deliberately corrupted artifacts required to fail. These exact
finite checks authenticate the literal data; they do not replace the
unbounded arithmetic proofs.
