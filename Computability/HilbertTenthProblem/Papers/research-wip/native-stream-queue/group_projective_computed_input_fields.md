# The radix region pays for two positive input-field projections

The complete [coupled-linear compiler](group_projective_coupled_linear_unit.md)
can compute its two native input fields F1,F2, removing **two comparisons
and two strictly positive witnesses** at unchanged certificate cost.
The single SOS polynomial saves **two multiplications and four additions**.
The exact degree is unchanged.

Their computed expressions need not be positive on arbitrary supplied
tuples. Positivity is instead proved from the retained outer scalar
bounds before invoking any native norm, sign, or typing theorem. The
highest packed radix region has output zero and makes both differences
strictly positive. Thus the elimination is a positive zero-set graph
bijection with the immediate parent, not an assumption that subtractions
preserve the positive domain.

Keep the fixed-table parameters and positive compiler numerals, including
`alpha+beta+1>=m`, and write

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1,
    nu=1+chi.

The complete successor bounds are

| Computed native fields | Certificate | Equations | Positive witnesses | SOS polynomial | Exact degree |
|---|---:|---:|---:|---:|---:|
|a,d,k,s, plus F1,F2|C+4|12-chi|m+31-chi|C+39-3chi|24nu L+54|
|a,c,d,k,r,s, plus F1,F2|C+4|10-chi|m+29-chi|C+33-3chi|nu(40L+2m+30)+60|

For the illustrative ten-letter table, the six-field option with both
optional projections gives **262 certificate operations, 9 equations,
44 positive witnesses and a 288-operation polynomial of degree 3544**.
Without controller-mask reuse, it gives **263/289 operations and degree
2904**, with the same equation and witness counts. No numerical universal
alphabet is instantiated; the separate 75/88 frontiers remain unchanged.

## 1. Exact source substitution

The parent has the positive supplied fields F1,F2 and port comparisons

    input_A=F1+F3=padded_A=16H+12,
    input_B=F2+F3=padded_B=16M+10,
    F3=16Z+8.                                    (1)

Replace the two existing port additions by the two subtraction gates

    computed_F1=padded_A-F3=16(H-Z)+4,
    computed_F2=padded_B-F3=16(M-Z)+2.             (2)

Every use of supplied F1,F2 is replaced by the corresponding computed
register. Every use of old input_A,input_B is replaced by padded_A,
padded_B. In particular the shared checksum still reads the correct
input sum without an additional addition. Delete the two comparisons
in (1) and the two supplied coordinates, then topologically order the
same number of gates. The joined inputs H,M,Z and q do not depend on
either native input field, so this ordering is acyclic.

The [source](group_projective_computed_input_fields.py) checks the actual
parent gate patterns and aliases, rather than applying an informal
substitution to just the displayed equations. For every integer supplied
assignment, let the restored parent F1,F2 have the values (2). Both old
port residuals vanish identically, every remaining residual agrees,
and the complete old and new SOS outputs are equal. This signed
polynomial identity does not itself assert that restored fields are
positive; that assertion is established next on the required zero set.

## 2. The retained outer equations suffice for positivity

Let `E_e=Ehat_e-1>=0`, `Z_i=Zhat_i-1>=0`. The unchanged raw edge
checksum defines `J=sum_e E_e>=0`. The retained or computed repunit and
joint positive bound say

    P=(B-1)J+1,
    sum_i H_i+sum_i Zhat_i+b=P+1, b>0.            (3)

Here all four H_i and all eight Zhat_i are supplied positive integers.
The parent input definitions give `D=u+height_slack>=4`, `B=16D>=64`.
The joint bound gives P>=12. If J=0 the repunit would give P=1, so
J>=1 and P>=B. These facts use no native norm or selector typing.
They imply

    0<H_i<P, 0<=Z_i<P, 0<=E_e<=J<P.

Every physical S_i is a sum of a subset of the E_e, hence
`0<=S_i<=J`. Define the mathematical abbreviations already represented
by the literal source:

    Hb=sum_(i=0)^7 H_(floor(i/2) xor 1) P^i,
    Zb=sum_(i=0)^7 Z_i P^i,
    Mb=(B-1)*sum_(i=0)^7 S_i P^i,
    Hc=sum_(e=0)^(m-1) E_e P^e,
    Mc=J*sum_(e=0)^(m-1) P^e,
    T=P^(m+8), T2=P^(L-2).

The exact scalar lane bounds give `Hb,Zb,Mb<P^8` and `Hc,Mc<P^m`.
All these values are nonnegative. The optional range width is eight
lanes or m lanes, and m>=8 is required when the latter is used. Thus
`T2>=T*P^8`. The joined output is

    Z=Zb+P^8*Hc+T*Hb<T*P^8<=T2.                 (4)

The joined inputs have the same highest radix region as in the parent:

    H=Hb+P^8*Hc+T*Hb+T2*B,
    M=Mb+P^8*Mc+T*Rb+T2*(B-1),                  (5)

where the range mask Rb is nonnegative. Therefore

    H>=T2*B>Z,
    M>=T2*(B-1)>Z.                              (6)

Equations (4)-(6) prove both fields (2) strictly positive. In fact
the restored residues are F1=4 mod16 and F2=2 mod16. This proof needs
neither dyadic P or B, Boolean controller cells, selected-source
identities, the strong Pell comparison, nor a recovered unit sign.
Those conclusions can safely follow after positive restoration.

The outer bounds are essential to this argument. We have not proved
positivity of (2) on arbitrary off-zero tuples, and we do not weaken
or omit the retained joint bound. The earlier output-bound obstruction
therefore remains excluded.

## 3. Complete positive equivalence

At every positive zero of the successor, (3) and the fixed input
definitions imply (4)-(6). Restoring the two fields using (2) gives
strictly positive parent coordinates. The two deleted comparisons
are identities, and all other residuals are identical. The full parent
proof, including conditional checksum normalization, now applies with
its original positive hypotheses.

Conversely, at every positive parent zero, (1) makes its F1,F2 equal
the unique values (2). Erasing the two coordinates therefore gives a
successor zero. These restoration and erasure maps are inverse on
positive zeros of the immediate coupled-linear parent. All outer
fields, input x, fixed compiler numerals, and program interpretation
are unchanged. This local graph bijection does not reclassify the
earlier coupled-sign normalization as a bijection.

The result is a complete fixed-table theorem, and it inherits the
same ordinary-input universal interpretation for the special fixed
alphabet from the padded enumeration. No new bit-selection or history
condition is unpaid.

## 4. Counts and exact degree

Each former addition in (1) becomes one subtraction in (2). All
other arithmetic gates remain, so the certificate's M/A split is
unchanged. Two fewer equations remove two residual squares, two
residual subtractions and two summation additions from the SOS.
Exactly two positive supplied coordinates disappear. The SOS splits
are consequently

    four: M=m+2h+97+f_M-d_M-epsilon-chi,
          A=2m+h+p+127+f_A-d_A-2chi;
    six:  M=m+2h+95+f_M-d_M-epsilon-chi,
          A=2m+h+p+123+f_A-d_A-2chi.

No defining equality is free in these counts; both subtraction gates
are present in the audited schedule.

Degree is measured before imposing any equation. Both new input fields
have degree at most `nu(L-2)+1`, which is strictly below degq=nu L.
For the range-mask body the bound follows from
`nu(L-3)+2<=nu(L-2)+1`; the highest radix term has the latter degree.
Therefore the checksum unit Q retains its highest form q*. In the
packed native index, the new q^2 F2 and q F1 terms have degrees at
most `nu(3L-2)+1` and `nu(2L-2)+1`. They are strictly below the
existing leading q^3 F3 term, of degree `nu(3L+m+15)+1`.

Thus every one of the six native unit factors retains the exact
highest form proved in the coupled-linear packet. The largest product
residual remains unique, and its square has the same nonzero highest
homogeneous part. The opening degrees are exact. This argument uses
the actual substitution degrees, not any on-zero bit or power identity.

## 5. Checks

The [receipt](group_projective_computed_input_fields.json) stores twenty
compact ledgers and one complete ten-letter source. Across these
variants, 1,280 complete graph/residual/SOS identities include 320
signed supplied assignments. The checker restores the computed F1,F2
and verifies every retained register and residual against the actual
parent, including both old port identities. Twenty exact weighted
offset evaluations check every residual degree and all six individual
unit highest coefficients, without expanding the redundant final SOS.

Another 768 fixtures impose only the raw edge checksum, repunit and
joint positive bound. They directly verify the joined-region bounds
and strict positivity of both restored fields, including J=1 and
nondyadic scales. They do not impose the native norm equations,
Boolean controller, bitwise AND or history transports. This isolates
the pretyping positivity obligation rather than testing it only on
already valid computation traces.

Run the checker normally for deterministic receipt comparison or
with `--write` to regenerate it. Parent sources and receipts remain
unchanged.

Independent review checked the pretyping positivity inequalities, source
substitution and degree argument, replayed the default receipt, and
verified another 256 signed complete residual/SOS identities across
both field variants and both optional compiler switches.
