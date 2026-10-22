# Smaller neighborhood compilers for the same blank K215 language

Source pin: `3b201cdea32d2c816f5f3d20734051f25fd3ef14` in VladimirReshetnikov/ProveIt.
Parent construction: `con-zfc-diophantine-forms/06-blank67`.
This is an ordinary mathematical proof with finite checks, not a Lean/Rocq formalization.

## 1. Unchanged semantic core

Use 06's 439 tile symbols, completed 216-state K215 table, and the exact local
predicate in `blank_helical.local_valid`. The four corner entries of its
3-by-3 argument are never used. Only the cross `(N,W,C,E,S)` matters.
The alphabet of center-valid crosses has exactly 38,256,607,897 elements.
The former 3-by-3 alphabet is its Cartesian product with four arbitrary
439-symbol corners, so this removes a redundant factor 439^4 exactly.

Enumerate the valid crosses with Start `(438,434,435,436,1)` first,
excluded cross `(438,0,437,438,437)` second, and all others lexicographically.
Both are locally valid by the same calculation as 06. The excluded cross is
globally impossible: its north tile H has vertical bit 0 while its center V
has vertical bit 1, contradicting vertical propagation at the north tile.
Every initialized Q has precisely the Start cross: its adjacent phases
must be L and R, and K215's first transition writes 1 at the center.

For selected crosses U_i in a cyclic group Z/NZ, impose

    U_i.E = U_(i-1).C,  U_i.C = U_(i-1).W,
    U_i.S = U_(i-h).C,  U_i.C = U_(i-h).N.

Writing a_i=U_i.C recovers U_i=(a_(i+h),a_(i+1),a_i,a_(i-1),a_(i-h)).
Thus the pullback tile plane at (x,y) is a_(-x-hy), and every actual cross
is locally valid. No divisibility, relative-primality or distinct-offset
assumption is needed. Conversely any locally valid plane with this cyclic
presentation gives these equalities. Start rules out h=0 modulo N since its
north tile and center differ. The finite initialized halting rectangle
proof and independently padded helical completeness construction of 06
therefore apply unchanged.

## 2. Exact reduced native layout

Let a=439, k=38,256,607,897, and let

    P=((0,1),(1,0),(1,1),(1,2),(2,1)),
    V=((0,1),(1,1)), H=((1,0),(1,1)).

Here P lists the retained payload positions, and V,H list overlap targets.
Set ell=max(2,bits(k+1)), A0=2^ell,

    p=max(0,ceil((k-2ell-9a-4)/2)),
    jmax=5a+4+p, mu=A0-2+sum_(j=1)^jmax A0^j,
    m=2ell+14a+8+2p, npos=m+1,
    ndum=npos-k-5a-4,
    e*=k+12a, M=k+15a+ndum, Emax=27M,
    Hc=Emax+24M+3a+1,
    T1=Hc+2Emax+a+1, T2=T1+4Emax+2.

Let L be the least power of 5 at least T2+2Emax+2. Retain the old payload
exponent

    e(r,c,u)=k+3a+(2-r)3a+(2-c)a+u,

only for (r,c) in P. Give it the compact clause index
j(r,c,u)=1+a*index_P(r,c)+u. Use k selectors, these 5a payload positions,
ndum consecutive dummies beginning at e*, and anchors M,3M,9M,27M.
Their disjoint union E has cardinality npos. The clause coefficient is

    c_i=1+sum_((r,c) in P) A0^j(r,c,U_i[r,c])
             +sum_(t=1)^4 A0^(5a+t)

at a selector, A0^j at a payload, A0^(5a+t) at anchor 3^(t-1)M,
and zero at a dummy.

Set

    U0=4(npos+2)(28(k+5a+4)+6)+8,
    bmin=max(ell(jmax+1)+3, ell(5a+4)+bits(U0)+1, 4).

Let b be the least power of 5 at least bmin, r=2^b, d=bL, B=r^L. Define

    DC=r^(3a)+r^(Hc+a)+r^(8M)+r^(24M)
       +sum_(e in E) c_e(r^(T1-e)+r^(T2-e)),
    DR=r^Hc,
    MF0=mu(r^T1+r^T2)
       +sum_((r0,c) in V,u<a) r^e(r0,c,u)
       +sum_((r0,c) in H,u<a) r^(Hc+e(r0,c,u))
       +r^(9M)+r^(27M),
    MC=B-1-sum_(e in E, e!=1)r^e-2r^e*,
    MF=MF0+4.

The four polynomial ports are B-1, K=DC+B*DR, MC, MF+B-1, with exactly the
same arithmetic interpretation as 06.

## 3. Why the native compiler proof still applies

The five payload groups use the same spatial embedding as the old nine.
At every retained vertical target e(r,c,u), multiplication by r^(3a)
selects exactly payload e(r+1,c,u). At every retained horizontal target
Hc+e(r,c,u), r^(Hc+a) selects exactly e(r,c+1,u), while DR selects the
right window's e(r,c,u). All four source/target pairs belong to P.
The old band separation and anchor inequalities are unchanged in form;
discarding corner payloads cannot introduce a new source at a tested
position. Selectors stop below k, payloads lie below k+12a, and dummies
remain above them, so none contaminates a retained copy target.
The sparse checker verifies these equalities for every native basis bit
at every tested field position in its finite fixtures.

There are now 4a copy parity tests. Thus

    pc(mu)=ell+5a+3+p,
    pc(MF0)=2pc(mu)+4a+2=m.

The adjusted dummy census npos=m+1 restores precisely the required mask
population balance. Consequently MC=2 mod 4, MF=4 mod 8,
0<MC,MF<B-1, and pc(MC)+pc(MF)=d, exactly as in 06.
The coefficient mass bound remains valid with 5a in place of 9a:

    sum c_e <=14(k+5a+4)A0^(5a+4).

This follows by counting at most k selectors, 5a payloads and four anchors;
each coefficient is bounded by the displayed positive geometric sum.
The choice of b supplies the parent's quarter-radix carry margin.

The clean-band proof uses only E within [0,Emax], the two band separations,
and that dummy e*+1 is below Emax. The anchor proof uses only the unique
18M difference between 9M and 27M. Both remain true. Therefore the transport
field synchronizes to a whole-cell temporal shift before any overlap is
decoded. The four retained copy groups give exactly Section 1's four
equalities. A selected cross has one tile indicator at each retained
position, an empty cell has none; the horizontal E/C comparison alone
propagates occupancy through the entire cyclic word from the marked Start.

The five-adic correction is still identically 3: T2-T1=4Emax+2 makes the
paired clause sum vanish modulo 5, and a=439=3 mod 4 gives
2DC-DR=3 mod 5 from the same four monomials. The Boolean dummy proof is
unchanged. Canonical tableaux have one Start and a nonzero temporal stride;
these ensure the exceptional origin field-mask test. Dummies are above
the low selector fields. The same carry estimate yields 2C+F<q/3 and hence
strict positive alpha=q-C-F after tuning the actual rank. Thus both
arithmetic soundness and completeness hypotheses of 06 are preserved.

## 4. Concrete geometry and verified scope

The executable formulas give

    ell=36, p=19128301935, jmax=19128304134,
    m=38256610096, npos=38256610097, ndum=1,
    M=38256614483, Emax=1032928591041,
    Hc=1951087339951, T1=4016944522473, T2=8148658886639,
    bmin=688618948863,
    b=5^17, L=5^19, d=5^36=14551915228366851806640625.

For b, 5^16=152587890625<bmin<=762939453125=5^17.
For L, 5^18=3814697265625<T2+2Emax+2=10214516068723
<=19073486328125=5^19. These prove the asserted minimal powers directly.
The bit length of B-1 drops from 5^67 to 5^36, a factor 5^31.
Both are still enormous and have not been expanded.

`count_blank_alphabet.py` was rerun with the exact-hash K215 source. Its
thirteen center categories exhaust all 439 center symbols and compare the
closed formulas against the local predicate for every left/right pair.
The resulting exact cross count is 38,256,607,897. The original source's
four unconstrained corners justify the factorization independently of
this implementation. The sparse compiler checker verifies support,
coefficient, population and congruence conditions on small fixtures; it
does not enumerate the actual giant alphabet. The parametric argument
above, not those fixtures, is the general correctness proof.

## 5. A further four-site option

The original initialization test says that an interior cell has a phase
iff its predecessor in time is H. Translate just this presence test one
row forward: a following interior cell has a phase iff the current cell
is H. Keep endpoint/phase-neighbor rules at the current center when that
center has a phase. This leaves only the four-site tuple (W,C,E,S).
All other clauses already use these four sites. Because a time translation
is bijective in every periodic plane (and in the full plane), imposing
the translated test at all centers is exactly equivalent to imposing the
old presence test at all centers. This is an equivalence of complete local
languages, not a restriction to canonical computations.

The exact executable relation is `tshape_helical.local_valid`. Its Start is
(434,435,436,1). Its excluded selector is (437,438,437,435): center H,
left/right V and following Q. This tuple passes its own center predicate.
In any global extension, both V neighbors propagate down, so the following
Q has a V to its left, forbidden by the initialization endpoint condition.
Thus exclusion removes no genuine computation.

The lifted overlap relations are only

    U_i.E=U_(i-1).C, U_i.C=U_(i-1).W, U_i.S=U_(i-h).C.

They recover each tuple from central tile a_i as
(a_(i+1),a_i,a_(i-1),a_(i-h)). Hence the same reconstruction, arbitrary-period
soundness, rectangle extraction, padding and dummy proof apply. Start
excludes zero temporal stride because its center Q differs from its
following symbol 1.

Use P=((1,0),(1,1),(1,2),(2,1)), V=((1,1),), H=((1,0),(1,1)).
There are 4a payload groups and 3a copy tests. Replace the scalar formulas
by

    p=max(0,ceil((k-2ell-7a-4)/2)),
    jmax=4a+4+p, m=2ell+11a+8+2p,
    ndum=m+1-k-4a-4.

Use 4a throughout the compact clause indexing, coefficient mass estimate
and U0 definition. All other layout formulas are unchanged. Section 3's
proof applies verbatim, with 3a copy groups and the three overlap equalities.
The next section records its exact count and geometry after direct checks.

## 6. Four-site count and geometry

In the completed table, among the 438 non-H symbols there are li=349
incoming-from-left symbols, ri=82 incoming-from-right symbols, ln=89
nonincoming-from-left symbols and rn=356 nonincoming-from-right symbols.
Q is included in li. The counts for the four-site relation are:

| Center type | Multiplicity | Allowed tuples per center |
|---|---:|---:|
| V | 1 | 439*438 = 192282 |
| H | 1 | 6*439 = 2634 |
| Headless bit 0 or 1 | 2 | 439*438+ln*rn+li*rn+ri*ln = 355508 |
| Halt head, bit 0 or 1 | 2 | 439*438+ln*rn = 223966 |
| Working head | 430 | 162788 |
| Initial L | 1 | 2*439+2*(ln+li) = 1754 |
| Initial Q | 1 | 437 |
| Initial R | 1 | 2*438+2*(ln-1+li) = 1750 |

For H, the right neighbor is H or V, the left neighbor is arbitrary,
and the following symbol must be L,Q or R. For headless centers, a final
H contributes 439*438 choices; otherwise there may be at most one
incoming head and its following ordinary symbol is determined uniquely.
For a halt center, its own staying head excludes all incoming neighbors.
For a working head, a final H is forbidden. Its escape direction removes
one nonincoming boundary choice, so either
(ln-1)*rn+li*rn+ri*(ln-1) or ln*(rn-1)+li*(rn-1)+ri*ln
is allowed. Both equal 162788 because ln+li=rn+ri=438.
For initialization centers the phase graph fixes the available right
neighbors, and the left-boundary endpoint restriction distinguishes L
from R. The same deterministic-update count gives the last three rows.
These eight rows exhaust all 439 tile symbols and sum to

    k=71,356,645.

`tshape_helical.py` independently checks these formulas by calling the
actual four-site predicate on every left/right pair and all possible
following symbols (represented by the exhaustive allowed-output list),
for the same thirteen center classes used by 06. It passed with the
exact-hash K215 table; no giant window list was materialized.

The scalar recipe yields

    ell=27, p=35676757, jmax=35678517,
    m=71358405, npos=71358406, ndum=1,
    M=71363231, Emax=1926807237,
    Hc=3639526099, T1=7493141013, T2=15200369963,
    bmin=963319989,
    b=5^13, L=5^15, d=5^28=37252902984619140625.

Indeed 5^12=244140625 < bmin <=1220703125=5^13,
and 5^14=6103515625 < T2+2Emax+2=19053984439
<=30517578125=5^15. The bit length of B-1 is now 5^28, reducing the
parent's 5^67 by a factor 5^39. This is a coefficient-height improvement
under the same four-port arithmetic interface, still far from practical
materialization. No extra existential variable or input coefficient is
introduced.
