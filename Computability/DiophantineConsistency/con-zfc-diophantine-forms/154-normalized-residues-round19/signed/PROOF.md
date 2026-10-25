# Round 19: common signed spheres, odd radix, and exposed coordinates

## Fixed equations and logical scope

Every equation is the sum of the squares of its complete listed quadratic
residuals. All variables range over unrestricted integers.

| Endpoint | Variables | Residuals | Degree | Collected monomials | Height |
|---|---:|---:|---:|---:|---:|
| balanced244 (principal) | 244 | 176 | 4 | 5212 | 3968 |
| dimension243 | 243 | 175 | 4 | 19517 | 7680 |
| balanced247 (intermediate) | 247 | 179 | 4 | 5328 | 3968 |
| sparse250 | 250 | 182 | 4 | 4770 | 6709 |
| dimension246 | 246 | 178 | 4 | 21537 | 6144 |
| lowheight247 | 247 | 179 | 4 | 10422 | 3840 |
| exposed247 (lifting source) | 247 | 179 | 4 | 4889 | 170496 |

These are achieved tradeoffs, not global minima. In ordinary ZFC, each
polynomial has an integer zero if and only if there is a finite ZFC
refutation. Negation gives the requested equivalence with Con(ZFC). This
is not a consistency proof, an assertion of unsolvability independent of
ZFC, or a new end-to-end proof-assistant endpoint.

The literal arithmetic input is `sources/common252.json`, byte-identical
to `inherited_common/equation/equation.json`. That 252-variable source and
its full portable arithmetic provenance are retained. Its main proof is
`inherited_common/proofs/NORMALIZED_REMAINDERS_PROOF.md`; the ordinary
calibrated signed C222 proof, orientation-first recovery and strict-budget
proof are retained under `inherited_common/upstream`. The logical interface
is the identified C222/ZF/ZFC finite-refutation calibration, including
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

The present contribution composes three independently supported mechanisms:
common scaled remainders, an odd-square radix, and exact residual-coordinate
simplifications. No additional undecided coefficient or exponent operation
is introduced. All exponents below describe the proved meaning of existing
quadratic power graphs, not operations in the final equations.

## 1. The common normalized-remainder interface

The unchanged semantic coordinates satisfy t=16+h0^2, V=(F^2+1)^t,
y=V(V-1), and the endpoint identities

    x=F+1+(y+1)u0,
    x=1+[1+(t+1)y]ut.

The initial nonnegative ceiling witnesses r0,s0 give

    B=r0+s0+1,   FB=V+s0.

The actual representatives are a,b,c,d,S,Sp,u,v,C0, and
H=1+their sum. The strict-budget power requests include N=B^x and
q=(BH)^x. All eighteen power graphs and all canonical Pell-orientation
conditions are unchanged.

The eleven digit denominators are L_i in {q^t,q^(t+1),q^(y+1),q^x}.
Let M=q^x. Three ratio coordinates satisfy L_i v_i=M for the three
smaller distinct denominators; for L_i=M use v_i=1. The numerator equations
have the form

    v_i U_i = M Q_i + R_i.

For a range numerator Q_i=N h_i; for the factorial numerator its actual
registers express Q_i=B+q h_i. The factor N M is shared among all range
rows. The normalized remainder R_i occurs only in its digit equation and
norm bound, never in the Pell frame. Once powers are recovered, x is at least
every denominator exponent (strictly larger for the three smaller levels), so L_i>0, M>0 and v_i=M/L_i are positive
integers. The equation implies v_i divides R_i. Thus r_i=R_i/v_i is an
integer, and division restores the original equation U_i=L_i Q_i+r_i.
This is an integer divisibility proof, not the insertion of rational
variables into a polynomial.

## 2. Replacing the initial radix sign guard

Remove only the ternary sign certificate for q-B-1. Replace it by

    q=(2z+1)^2.

Three private guard coordinates disappear and one unrestricted integer z
is introduced, saving two variables. The incoming coordinate translation
has semantic q=stored q-1, so the literal uncentered-looking new row is
stored q-4z^2-4z-2. `verify.py` derives this from the recorded translation
and checks the exact old sign guard; no shift is guessed.

The soundness order is as follows.

1. The unchanged signed frame and semantic anchor canonically orient both
   coordinates of every principal Pell pair before any of the eleven
   remainder signs or the removed radix guard is used. The inherited power
   lemma is valid for signed exponents and signed Pell center: at base n>=2
   it excludes a negative index k, since the bounded modular identity would
   imply m n^(-k)=1. For known k>=0 it also handles base one.
2. The unchanged t request at base F^2+1>=1 gives V=(F^2+1)^t. The retained
   r0,s0>=0 imply B>=1, F>=1, FB>=V>=F^2+1, hence B>F and B>=2.
   Consequently V< B^2 and y=V(V-1)>F+2.
3. The existing request N=B^x now has base B>=2, so x>=0. If u0<=-1,
   the first endpoint would give x<=F-y<0. Thus u0>=0 and x>=F+1>=2.
   The second endpoint gives ut>=1 and x>=2+(t+1)y, in particular x>=8.
4. The new square row gives q>=1, so q+1>=2. Requests at base q+1 force
   all nine representative exponents nonnegative; H>=1 follows.
5. The base BH>=2 is now valid, and the retained request yields
   q=(BH)^x>=B^2>B. Thus the removed output-slack sign is recovered. All
   other requests, the positive denominators and the normalized ratios
   now have their usual meanings. No remainder bound or factorial
   interpretation was used in these deductions.

For completeness, the parent's cofinal construction permits x even:
y is even, so every beta CRT modulus 1+(i+1)y is odd, and an odd common
multiple can be added to choose any required parity at an arbitrarily
large positive representative. Take F=t!. Each factor 1+F^2/i is odd,
so B and N are odd. Modulo the odd product N^2 each independent actual
representative admits either parity. Choose a,b of opposite parity as
required by the old anchor. Choose one of the other seven representatives'
parities so the total sum is even, hence H is odd. The old bounds are
preserved: ordinary representatives can lie in (0,2N^2], and dominant a
in [2N^2,4N^2). All old CRT values, frame estimates and anchor-completion
conditions are unchanged. Since BH is odd and x even, put
z=((BH)^(x/2)-1)/2. This is an integer and supplies the square row.
This proves existence of compatible witnesses; it does not falsely assert
that every old zero has an odd-square radix.

## 3. A smaller common sphere

Write G(A,B,C)=A^2+B^2+C(C+1). This is nonnegative at all integer triples
and represents every nonnegative integer. Indeed the three-square theorem
represents 4n+1, with exactly one odd coordinate; writing its coordinates
as 2A,2B,2C+1 gives the stated representation.

Replace the incoming norm equation

    M^2-4 sum_(i=1)^11 R_i^2-1 = G(A,B,C)

by the simpler equation

    M^2-2 sum_(i=1)^11 R_i^2 = G(A,B,C).                (S)

For any new zero, 2R_i^2<=M^2, hence |R_i|<3M/4. Since R_i=v_i r_i
with v_i=M/L_i>0, this gives |r_i|<3L_i/4.

For the factorial digit the canonical low tail is already small before
factorial recovery. For m>=1,t>=1 and 0<=j<=t,

    binom(m+t,j)<=(m+1)^t.

Induct on t using Pascal for the interior; at the new last position use
binom(m+t,t)=product_(i=1)^t(1+m/i). Applying m=F^2 bounds every required
coefficient by V. Since V<B^2 and q=B^x H^x with x>=8,

    V/(q-1)<2/B^(x-2)<=1/32.

The geometric sum therefore bounds the canonical factorial tail by
0<=rho_f<L_f/32. Both r_f and rho_f are congruent to the numerator modulo
L_f, and |r_f-rho_f|<(3/4+1/32)L_f<L_f. Thus r_f=rho_f. Reduction of the
restored quotient equation modulo q identifies B=binom(F^2+t,t), since
both sides lie in [0,q). The unchanged factorial fixed-point proof gives
F=t! only now.

The literal congruence B|C0+F^2+1 then excludes C0=0, hence H>=2.
Every ordinary upper representative a has coefficients at positions
j<=k<=x bounded by max(1,a)^k<=H^x. The repaired constructor ledger for
the derived label gives h<=H^ell, ell=4194304, and ell(t+1)<x, so its
needed coefficients satisfy the same bound. Since q=B^x H^x,

    H^x/(q-1)<2/B^x<=1/128<1/32.

Every remaining canonical low tail is therefore rho_i<L_i/32. The same
short-congruent-lift argument gives r_i=rho_i. In particular every deleted
old interval and quotient interpretation is recovered. Set the old slack
to L_i-rho_i-1>=0 and choose G witnesses for the nonnegative products.
The unchanged source now decodes a finite C222/ZFC refutation.

Conversely take the canonical witnesses of a finite refutation, with the
parities chosen above. Set R_i=v_i rho_i. Then 0<=R_i<M/32, and

    2 sum R_i^2 < (22/1024)M^2 < M^2.

The positive integer slack in (S) has a G representation. This proves
completeness of the new sphere. The weaker already available rho_i<L_i/8
would suffice as well, since 22/64<1; no margin at equality is needed.
The sphere is precisely the recorded domain_guard.4 row; the other sphere
(domain_guard.3, for Pell orientation) is untouched.

## 4. Reversible algebra and exact projection

The subsequent transformations are finite polynomial identities. For a
residual list (f_i), the operation f_i <- f_i+k f_j with i!=j and integer k
is inverted by subtracting k f_j. Thus the common zero set is unchanged,
although the sum of residual squares, its support and height can change.

A coordinate shear x_j <- x_j+k x_i (i!=j) is an integer bijection with
inverse coefficient -k. The general triangular elementary form used in
the dimension endpoint has coefficient one on its own coordinate and an
integer linear form in the others, so the same inverse applies.

If a residual is exactly plus or minus (v-f), where f is an integer
polynomial of degree at most two not containing v, replace v by f in every
residual and delete that now-zero residual. For an affine f, every residual
remains quadratic automatically. For quadratic f, require that v occurs
only as a linear monomial in every other residual; substitution again
leaves every residual quadratic. Projection onto the remaining coordinates
is a bijection of common zero sets, with unique integral restoration v=f.
The verifier checks the exact unit equation and the only-linear-occurrence
condition before every deletion, explicitly checks every resulting degree,
and gives all restoration polynomials in the frozen certificate. It never
divides by a nonunit coefficient.

The initial exposed247 transformation removes three affine coordinates.
The principal balanced244 then removes three more coordinates whose
restoration polynomials are quadratic: mul.281, add.292, and mul.194.
Each appears only linearly in every other residual at its deletion step.
Thus 250 becomes 244 and 182 rows become 176. Nine further invertible
row additions improve support from 5217 to 5212 and height from 4192
to 3968. This endpoint dominates the balanced247 checkpoint.

The smaller dimension243 also eliminates add.380 by an affine restoration
with 15 terms, before its three quadratic deletions. It has seven total
projected coordinates (four affine, three quadratic) and 175 residuals;
its denser quartic is an explicit cost of saving a variable. The independent
legacy dimension246 alternative uses four affine projections, trading
higher variable count and support for lower height than dimension243.

Each stage compacts the retained coordinates in ascending original order.
This is merely a renaming. Projected coordinates are restored in REVERSE
elimination order by their recorded v=f formulas, not arbitrarily as zero.
Only genuinely unconstrained obsolete coordinates can be filled freely;
the semantic old guard auxiliaries are instead refilled using their proved
nonnegative ternary representations. Full final polynomial expansions
occur AFTER compaction, and every live coordinate index is checked.

## 5. Artifact verification, provenance, and limitations

`build.py --check` reproduces every final JSON byte from pinned source and
fixed operation certificates. `verify.py` independently reconstructs the
semantic row changes, all coordinate and row inverses, every polynomial
restoration, every collected coefficient and every metric. It imports no
builder or predecessor algebra module. Normal and optimized Python runs
pass the same explicit checks, including deliberate malformed residual,
restoration and noninvertible-operation controls.

The common-normalization input, its complete original checker and its
ordinary proof dependencies are under `inherited_common`. The exact shared
shear history and the predecessor affine-exposure certificates are retained
in `provenance`; their transforms were transported by semantic coordinate
names and exact row polynomials, not ambiguous repeated row labels. The
new height-aware residual operation traces are literal frozen certificates;
no optimization search is needed for replay.

Finite computation authenticates these particular polynomial artifacts.
The unbounded existence/nonexistence equivalence rests on Sections 1--3,
the retained source arithmetic proof and the named logical calibration.
No finite test, measured coefficient bound or failure to find a solution
is being used to infer consistency, global optimality or undecidability
of any unrelated question. All new material was prepared with AI assistance;
inherited notices and licenses remain retained.
