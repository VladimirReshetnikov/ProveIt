# Coordinated polynomial coordinates: 21/16, 20/18, and 19/40

## Main conclusion

This component gives three fixed ordinary integer polynomials, with
unrestricted integer unknowns:

| Packet | Unknowns | Residuals | Exact total degree | Inspected incoming point |
|---|---:|---:|---:|---:|
| coordinate21_degree16.json | 21 | 9 | 16 | 21 / 20 |
| coordinate20_degree18.json | 20 | 8 | 18 | 20 / 32 |
| coordinate19_degree40.json | 19 | 7 | 40 | 19 / 88 |

Each polynomial is the sum of squares of all listed residuals. Its integer
zero set is connected to the calibrated incoming 25-integer octic by
explicit polynomial bijections, integral changes of coordinates, and
reversible elementary row operations. Composing with the named inherited
ordinary compiler/Pell/calibration theorem yields the ZFC-provable
equivalence between absence of integer zeros and Con(ZFC). Neither
consistency nor absence of zeros is asserted or assumed here.

The full LaTeX account, including the compact equations, is
coordinate_section.tex. The baseline PROOF.md reproduces older source
mechanisms. Those baseline sizes are not claimed as new results.

## 1. Exact input calibration and the row bridge

The six fixed numerals are beta=2^1064921-1, the complete source-34
K0,MC,MF tuple (MF already shifted), A=2^1113, B=2^666104.
They are provided as actual byte payloads with a finite reconstruction
recipe, not left as parameters. Their binding is COEFFICIENT_BINDING.json.

The inert incoming packet incoming_joint25.json is extracted exactly from
ZFC_Diophantine_Joint_Guards_2026-10-24.zip. Our independently reconstructed
baseline octic25 uses the same coordinates and same zero set, but arranges
three rows differently. Put epsilon=V-jc+eta+zeta-1-hE. This is incoming
row11, using zero-based indexing. First permute incoming rows in the order

    0,1,2,3,4,5,6,7,11,8,9,10,12.

Then add (E-a)epsilon to row2, -E(c-eta)epsilon to row3, and epsilon to
row5. Keep epsilon unchanged at its new position8. This replaces the
incoming abbreviation 1-V+jc+hE by eta+zeta in the three rows. All
thirteen polynomial identities are checked exactly. Subtracting the same
multiples inverts the operation, so the zero sets agree over every
commutative ring; there is no reliance on numerical sampling.

## 2. The 21-coordinate system

Unknowns are

    J3,C,z,f,h,r,v,w3,s,k,y,gamma,o,j,Y,c,I,t,p1,p2,p3.

Every unknown ranges over all integers. In the packet, v is v_scale,
s is tau_gap, t is pair_root, and pi is pair_posi. Define only polynomial
abbreviations:

    J0=3J3+1, W=4(3w3+1), q=beta J0+1, X=Wq,
    F=(K0+W)C-z(q-1), E=XY, a=(X+1)Y,
    eta=c-Yk, zeta=k-eta, V=fo-c,
    Delta=a^2+4a+3, D=X+ac+gamma(4a+3),
    R=(q-F)(q^3-q)-C(q^2-1)+(MC+qMF)J0,
    G=AFBC-(q-AF-BC)^2, Z=eta*zeta,
    T=1+p1^2+p2^2+p3(p3+1).

No abbreviation adds an unknown. The complete residual list is

    R1=Y-(2v+1)q^3,
    R2=s^2+(2s-k)EYk-1,
    R3=D^2-Delta*c^2-1,
    R4=k-1-hE-R,
    R5=V-jc+k-1-hE,
    R6=I-(2r+1)c^2,
    R7=I^2-Delta(f^2-1),
    R8=y^2-1-I^2(y^2-V^2),
    R9=GZ-(t^2-G-Z+1)^2-T.

The single equation Q21=R1^2+...+R9^2=0 has 21 variables. Residual degrees
are respectively 4,6,8,5,4,3,8,6,8. Z has highest-degree term -Y^2k^2,
so R9 has coefficient -1 at Y^4k^4; all other possible contributions are
of smaller relevant degree. Thus [Y^8 k^8]Q21=1 and degree(Q21)=16
on the actual fixed-coefficient slice.

## 3. Universal polynomial-bijection proof

In the convenient 25-variable baseline make the simultaneous triangular
changes

    C=q-F-alpha, Y=a-E, k=eta+zeta, s=tau-E(c-eta).

Their inverse formulas are

    alpha=q-F-C, a=E+Y, zeta=k-eta, tau=s+E(c-eta).

These changes are bijections of the full integer coordinate space.
Four source rows now determine four coordinates monically:

    F=(K0+W)C-z(q-1), E=XY, eta=c-Yk, V=fo-c.

Deleting these four rows and substituting their integer-polynomial right
sides gives precisely the nine displayed residuals. At the first norm,
put u=E(c-eta)=EYk and use the identity

    (s+u)^2-(k+u)^2+(k+u)k-1 = s^2+(2s-k)u-1.

This cancels the square of the degree-five expression u. It is an exact
ring identity, not an asymptotic estimate.

To map an old zero forward, take the four triangular coordinates and
forget F,E,eta,V. The four removed equations guarantee that the old
coordinates equal their indicated reconstructions. Conversely, at any
new zero restore F,E,eta,V by the displayed polynomials and invert the
triangular changes. Each deleted defining row is identically zero; each
retained row vanishes by its defining new equation. The two maps compose
to the identity on the zero sets. No division, denominator guard,
positivity hypothesis, or natural-number restriction is involved.

The structural reason for the lower degree is the choice to keep Y and k
as coordinates. Expanding them before eliminating F and E obscures the
quadratic formulas eta=c-Yk and zeta=k-eta. With them retained, both
G and Z have degree four and the joint positivity residual has degree eight.

## 4. Twenty variables at degree eighteen

Make the integral change y_old=fo+b, retaining unrestricted b, and eliminate
I=(2r+1)c^2 from Q21 by its monic row R6. This leaves twenty coordinates
and eight rows. Since V=fo-c,

    y_old^2-V^2=(c+b)(2fo+b-c).

The auxiliary residual becomes

    (fo+b)^2-1-(2r+1)^2 c^4(c+b)(2fo+b-c).

It has degree nine, and all other rows have degree at most eight. Its
square is the sole contribution to r^4 c^10 f^2 o^2, with coefficient64.
Therefore Q20 has exact degree18. The inverse restores I and y_old, so
the proof of equivalence is another integer-polynomial bijection.

## 5. Nineteen variables at degree forty

Now eliminate Y using the monic equation

    Y=(2v+1)q^3.

The nineteen unknowns are

    J3,C,z,f,h,r,v,w3,s,k,b,gamma,o,j,c,t,p1,p2,p3.

Use the common abbreviations, plus Y=(2v+1)q^3, I=(2r+1)c^2, and
y_old=fo+b. The seven residuals are R2,R3,R4,R5,R7,R8,R9; their exact
degrees are 12,14,7,7,14,9,20. The coefficient

    [v^8 J3^24 k^8]Q19 = 2^8 * 3^24 * beta^24 > 0

proves exact total degree40. It comes from substituting the highest-degree
part of Y into the earlier Y^8k^8 certificate. All non-guard rows have
degree at most14 and cannot affect this degree40 coefficient. Restoring
Y again supplies the inverse integer-polynomial map.

## 6. Comparison, verification, and limits

The comparison reads all six incoming archives supplied at the pinned
repository snapshot, in addition to numbered packages68-75. The incoming
Joint Guards package has21/20,20/32,19/88. The new21/16,20/18,19/40
points improve degree at those fixed dimensions by20%,43.75%, and
approximately54.55%, respectively. The existing25/8 and other reproductions
are not new. Other unrestricted and positive-domain frontier points remain
separate; no global or literature-wide minimum or priority is claimed.

build_coordinate_family.py checks all row operations, triangular changes,
deleted defining rows, compact display identities, coordinate liveness,
degree bounds, and nonzero degree certificates with exact integer
polynomial arithmetic. The checks run with Python assertions disabled.
The inherited source-34 coefficient recipe is replayed exactly; none of
the numerical coefficient ports is guessed or partially rebound.

The universal new equivalence is the polynomial-bijection argument above.
Its interpretation as finite ZFC refutability uses the inherited ordinary
compiler/Pell/calibration theorem. This component is not an end-to-end
Lean/Rocq proof or an internally encoded object-ZFC derivation. It does
not assert that any listed equation actually lacks a zero.

## Further questions

1. Can a further integer coordinate change lower the quartic-in-Y,k
   positivity cost after either coordinate is eliminated?
2. Can the auxiliary norm be reduced below degree nine after I elimination
   without increasing the strong-norm degree beyond eight?
3. Can an elimination optimizer search among coordinate changes and
   reversible row operations while emitting literal restoration certificates?
4. Can the source-34 calibration be replaced by the compact coefficient tuple
   with full signed-power and determinant completeness proofs?
5. Can these exact maps be added to the repository's formal arithmetic
   development without importing an unproved native/internal calibration?
