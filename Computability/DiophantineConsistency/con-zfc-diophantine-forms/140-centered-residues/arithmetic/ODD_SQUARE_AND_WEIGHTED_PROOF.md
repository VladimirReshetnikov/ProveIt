# Odd-square radix and a merged radius certificate

These two reductions extend `SIGNED_RADIUS_PROOF.md`. They retain the same
literal cofinal C222 source and ordinary refutation calibration. All quantified
coordinates are unrestricted integers.

## 1. Replace the initial output-slack certificate by an odd square

The source's only initial radix-sign certificate consists of

    q = B+o+1,          o = a^2+b^2+c(c+1).

It uses four private coordinates o,a,b,c and two rows. Replace it by the single
quadratic row, with one unrestricted coordinate z,

    q = (2z+1)^2.                                           (OS)

The original soundness proof used q>=2 too early to be copied verbatim.
The following reordered proof is required.

The signed Pell frame, anchor and orientation arguments use squares of all
proposed power atoms. They therefore apply before any sign or interpretation
of q. In particular the pair at the already positive index t>=16 is canonical.
Its request at base F^2+1>=1 gives V=(F^2+1)^t. At F=0 the base is one, which
is covered by the retained base-one case. The still retained factorial
remainder and slack guards give B>=1 and BF=V+s with s>=0. Consequently
F>=1, B>F, B>=2, and y=V(V-1)>F+2.

Use the exact-power request N=B^x next. Its base B>=2 is now available.
The signed-power lemma excludes x<0. The first endpoint then forces u0>=0
and x>=F+1>=2; the last forces ut>=1 and x>=2+(t+1)y.

Equation (OS) gives q>=1. Thus q+1>=2, and the requests at base q+1 force all
nine actual CRT representatives, and the derived label, to be nonnegative.
Hence H0=1+sum representatives >=1. Now the request q=(BH0)^x is decoded at
base BH0>=2, and it gives

    q >= B^2 > B.

This restores the deleted output slack o=q-B-1>=0, together with three fresh
square witnesses for it. In fact q>=4, and the odd-square condition makes
q>=9. All stages of the radius-margin proof now have their original premises.
There is no use of q>=2 in the earlier step that proves q>=2.

### Constructive completeness with both parity conditions

Take any finite refutation and the inherited cofinal horizon t=16+h^2 beyond
the required data. Put F=t!, V=(F^2+1)^t and y=V(V-1). This y is even.
Every beta denominator 1+(i+1)y is consequently odd. The endpoint moduli y+1
and 1+(t+1)y are odd as well. The CRT class of valid beta codes x therefore
has an odd period. Choose an arbitrarily large **even** x in this class.
The existing threshold conditions on x are preserved by choosing it large.

For every 1<=i<=t,

    F^2/i = F*(F/i)

is even because F=t! is even. Thus each reciprocal CRT factor 1+F^2/i is odd,
so their product B and the new precision modulus N^2=B^(2x) are odd.
Adding N^2 to a CRT representative preserves all required congruences and
flips its parity.

First choose the dominant representative a in [2N^2,4N^2) and b with parity
opposite to a. The existing construction has

    J = 1+a+b modulo 2,
    J >= 2a^2 >= 8N^4.

Thus its semantic anchor is even and retains its required dominance. Choose
the parity of a third independent representative, for example c, so that the
sum of all nine representatives is even. It can be chosen in (0,2N^2] with
the required CRT residues and parity. The other ordinary representatives
are chosen in the same interval. This makes H0 odd without changing the
parity of a+b or weakening the dominant-anchor estimate. The inherited
interval, precision, and semantic-anchor proofs all remain valid.

Now BH0 is odd and x is even. Therefore

    q=(BH0)^x = W^2,       W=(BH0)^(x/2) odd,

and z=(W-1)/2 is an integer satisfying (OS). Supply the unchanged canonical
Pell witnesses and the fresh radius gaps. This proves completeness.

The attained unweighted endpoint has 259 integer variables, 185 quadratic
rows, 5,361 collected quartic monomials and coefficient height 128,446.
Relative to the 261-variable radius-only form, the raw change removes three
coordinates and one row. The final projection loses one affine elimination
because q is now quadratic in z, so the attained saving is two coordinates.

## 2. Merge the first two radius groups

Let D=q^t and D'=q^(t+1)=qD. The original signed compiler supplies both exact
powers; their exponent metadata differs by exactly one. Their relation is
an arithmetic consequence after power recovery, not an extra assumed raw
identity.

There are two low residues r_1,r_2 at D, and five low residues s_1,...,s_5
at D'. Introduce just two multiplication wires u_i=q*r_i and replace the
two radius rows by

    D'^2 = 4*(u_1^2+u_2^2+sum_(j=1)^5 s_j^2)
           +1+a^2+b^2+c(c+1).                              (WR)

Both wire definitions and (WR) are quadratic. The canonical values obey

    0<=q*r_i^0<D'/15,       0<=s_j^0<D'/15.

Each u_i is congruent to q*r_i^0 modulo D' because r_i is congruent to
r_i^0 modulo D; each s_j has its usual congruence modulo D'. The radius
lemma works for any m<=56, because 4m/225<1. In particular it applies to
these seven residues. It gives u_i=q*r_i^0 and s_j=s_j^0. As q>0, the
retained multiplication rows then give r_i=r_i^0. Completeness follows
from the same three-square representation of the positive gap.

This replaces six gap coordinates by three and adds two multiplication
wires: one fewer variable, at the cost of one extra row. The selected
principal endpoint is therefore

    258 unrestricted integers;
    186 quadratic residuals;
    degree 4;
    5,366 collected monomials;
    coefficient height 128,446.

The 259-variable endpoint retains one fewer row and five fewer monomials.
They are distinct, fully supplied tradeoffs. The matched 282-variable
incoming equation had 192 rows and 5,491 monomials at the same degree and
height, so both new equations improve all of those varying size metrics.

## 3. Combined statement and verification boundary

The new raw polynomial system is obtained by exact private-coordinate
deletion, addition of the displayed quadratic rows, and unchanged retention
of all other inherited residuals. The new finite checker independently
reconstructs this mutation, including the full power-call metadata for
D'=qD. It then replays every integral monic projection, every fixed integer
translation and the complete quartic expansion. The proof above supplies
the unbounded arithmetic implications that finite checks do not establish.

Composed with the retained numerical C222/ZF/ZFC refutation calibration,
ZFC proves that each of these two literal quartics has no integer zero if
and only if Con(ZFC). No consistency decision, global minimum, or newly
completed proof-assistant development is claimed.
