# Shared arithmetic for the Report 35 and 36 finite-prism cubics

This packet emits 24 complete straight-line sources for three small prisms. Each
source includes every witness coordinate, local term, and final addition. Two
explicitly shared schedules compute exactly the same full polynomial: replacing
the five weighted edge squares by their first two moments and merging two vertex
products saves **V+4E multiplications and E additions**, hence **V+5E operations**.
The result is a variable-arity finite-prism calculation. It supplies no new
universal 84/85-operation bound, fixed-arity representation, loader audit, or
operation-optimality claim.

The companion [helper](sandpile_shared_arithmetic35_36.py) uses only the Python
standard library; the [receipt](sandpile_shared_arithmetic35_36.json) contains all
24 complete sources and zero witnesses. Archived Python is read as pinned text,
never imported or executed. This is a bounded replay CLI, not a maintained
arbitrary-input compiler API.

## 1. Sources actually read and authenticated

The complete composition proof, its actual vertex/edge formula source, and the
complete real-orthant proof were read. The helper checks these archive and member
SHA256 pins on every replay; the Report 36 approved-base source must also equal
Report 35's source byte for byte.

| Archive under `docs/incoming/` | SHA256 |
|---|---|
| `Literal_Periodic_Sandpiles_and_Diophantine_Certificates_Package.zip` | `3202b1f0430353a3cd05f15ac6f34e9a797ed931d9a86e3580a110d97b01a12d` |
| `Real_Exactness_of_Binary_Sandpile_Certificates_Package.zip` | `72cfb3a88640020e97f9b6b62c4f7580f97d75ed4f957b8c604536119bcf96ac` |

| Member | SHA256 |
|---|---|
| `Research_Report35/evidence/composition/PROOF.md` | `6e5a053e7f599a17ee77c49e3092e041c7ea3e0de62156095fe9ece5e761d60e` |
| `Research_Report35/evidence/composition/prism_certificate.py` | `bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2` |
| `Research_Report36/evidence/real/PROOF.md` | `9bc26062cc0e68fc8fee18290c347b309e2f711d208644ec541b29a5492071ae` |
| `Research_Report36/evidence/real/approved_base/prism_certificate.py` | `bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2` |

The inherited semantic theorem is the binary-odometer certificate on a specified
finite rectangular prism, with initially stable exterior. Its natural zero is
unique when a legal global stabilization with binary odometer supported in that
prism exists. Report 36 changes `fg` to `f(g+u)`, making every nonnegative-real
zero natural, with the same complete natural zero tuple. This packet checks the
literal polynomial interface and preserves those theorems by identities. It does
not independently audit a periodic sandpile loader or prove that every input has
such a prism or binary odometer.

## 2. Full polynomial and shared ports

For a prism of side lengths a,b,c, put V=abc, E=3V−ab−ac−bc and
H=2(ab+ac+bc). Each of the H distinct face-halo sites has one inward neighbor.
The number of natural witnesses is W=8V+6E+H. The declared fixtures have zero
exterior height and positive interior heights.

At a vertex, supplied coordinates are `(z,ell,f,k,c,beta,g,h)`, and the shared
ports are `u=k+c`, `r=u+c+beta`, and `f+k`. The rank port is emitted only when
used by an edge. With A and B the incident comparison counts, the original
vertex terms are

```
(z+6u−sum_neighbors u−eta)^2 + (z+ell−5)^2 + (f+u−1)^2
+ (f+k)beta + u(z−A−g)^2 + fg + c(B−z−1−h)^2 + (f+k)h.
```

The real variant substitutes `f(g+u)` for `fg`. A halo contributes
`(u_neighbor+halo_gap−5)^2`.

For an oriented edge v→w, put `d=r_w−r_v` and name its six coordinates
`lo,neg,eq,pos,hi,sigma`. Both schedules explicitly share

```
gap=sigma+2; ext=lo+hi; inner=neg+pos;
middle=inner+eq; S=ext+middle.
B_lower=S−lo; A_lower=B_lower−neg;
B_upper=S−hi; A_upper=B_upper−pos.
```

These comparison contributions equal the original selector sums as polynomial
identities, without assuming S=1. The vertex A and B ports sum these incident
contributions. Both schedules retain the edge terms `(S−1)^2` and
`middle*sigma`.

The direct schedule additionally sums

```
lo(d+gap)^2 + neg(d+1)^2 + eq*d^2 + pos(d−1)^2 + hi(d−gap)^2.
```

The moment schedule uses exactly

```
S*d^2 − 2*d*(gap*(hi−lo)+(pos−neg)) + gap^2*ext + inner.
```

Expansion proves equality over every commutative ring: the coefficients of d²,
d, and the constant part are respectively S,
`−2*(gap*(hi−lo)+(pos−neg))`, and `gap²*ext+inner`. No simplex, zero-set,
positivity, or integrality assumption is used. The merged vertex product is
`(f+k)(beta+h)`, also an unconditional identity.

The moment expression has signed intermediate terms. Its complete polynomial
remains exactly the original orthant-nonnegative polynomial; the intermediate
terms are not separately asserted nonnegative.

## 3. Literally paid schedules

An addition, subtraction, or multiplication of two available registers costs one
operation; squaring costs one multiplication. Constant, zero, and unit folds are
explicit in the emitter. Nonunit coefficient multiplication is paid; `2*cross`
is emitted as `cross+cross`. There is no automatic CSE or hidden reassociation.
Each source ends with exactly one addition per term after the first.

With common ports already available, the five direct weighted squares require
10 multiplications and 8 additions, including their four joining additions.
The moment block requires 6 multiplications and 7 additions. Merging the vertex
products saves one multiplication: the internal `beta+h` addition replaces one
final joining addition. Thus the full saving is (V+4E)M+EA. The number of displayed
terms drops by V+4E; these are summand counts, not a claim to delete that many
independent equations.

For the emitted connected rectangular fixtures, let I=1 for the singleton and
I=0 otherwise. The fully paid natural base schedules are

```
direct: M=11V+12E+H, A=21V+28E+3H−1−I;
moment: M=10V+8E+H,  A=21V+27E+3H−1−I.
```

The singleton exception omits its unused rank calculation and folds empty
neighbor sums. The real variant adds V additions, with no extra multiplication,
since u is already available. Report 36's original affine-expansion ledger
counts coefficient-times-variable multiplication even for coefficient 1. These
are different declared evaluation conventions; the present comparison is
between the two complete shared schedules above.

| Fixture and interior heights | V,E,H | W | Direct base M+A | Moment base M+A | Saved |
|---|---:|---:|---:|---:|---:|
| 1×1×1, 6 | 1,0,6 | 14 | 17+37=54 | 16+37=53 | 1 |
| 2×1×1, 6,5 | 2,1,10 | 32 | 44+99=143 | 38+98=136 | 7 |
| 2×2×2, one corner 6 and other sites 5 | 8,12,24 | 160 | 256+575=831 | 200+563=763 | 68 |

The corresponding direct→moment real totals are 55→54, 145→138, and 839→771.
These costs include all halo terms and the final sum.

Each old natural coordinate w can instead be represented by a positive integer
p_w, with w=p_w−1. The packet also emits this option, paying exactly W additional
subtractions and keeping W witnesses. It is a bijection between full natural
and positive-integer tuples. The shifted Report 36 real theorem applies on
**p_w≥1 for every coordinate**, not on the whole strictly positive real orthant
p_w>0, which would permit negative restored coordinates.

## 4. Independent expansion, exact degree, and genuine zeros

The helper separately reconstructs the original direct formula using affine
selector sums, without the moment identity or S-subtraction comparison ports.
It expands every emitted gate into a fully collected sparse integer polynomial
and compares the entire output coefficient dictionary against that reference.
The shifted reference independently expands every occurrence of p_w−1.

Every source has degree exactly 3. The reference coefficient of `v0_k*v0_z^2`
is 1, and affine translation preserves this top coefficient. The natural base
polynomials have respectively 55, 345, and 3,913 collected monomials, with
coefficient heights 212, 364, and 1,031. The real change is checked exactly as
`sum_v f_v(k_v+c_v)`; it preserves support and coefficient height on these
fixtures. Complete coefficient hashes and counts are saved in the receipt.

The complete natural witnesses are constructed independently by literal legal
threshold-six firing on the tiny prisms, then parallel support burning. Every
site fires once. In lexicographic vertex order, the final interior states and
burning ranks are

```
singleton: z=[0],                   r=[1];
pair:      z=[1,0],                 r=[1,2];
cube:      z=[3,2,2,2,2,2,2,2],    r=[1,2,2,3,2,3,3,4].
```

Every halo ends at height 1 and every site farther outside remains at zero.
Thus these are genuine globally stable endpoints with binary odometer, not
arbitrary algebraic tuples. All full sources evaluate to zero on their saved
complete witnesses; positive versions add 1 to every coordinate.

A separate exact fractional regression uses singleton eta=1,
`z=0, ell=5, f=5/6, k=1/6, c=beta=g=h=0`, and every halo gap 29/6.
Both base schedules evaluate to zero, while both real schedules evaluate to
5/36. This is deliberately a nonintegral false zero of the old base polynomial,
not an additional natural stabilization witness.

## 5. Receipt and replay scope

The receipt checks 24 complete sources (three fixtures, two polynomial variants,
two schedules, and two coordinate domains), all 8,788 paid gates for closure and
liveness, 24 entire coefficient identities, and 24 genuine zero tuples. Another
192 signed/rational evaluations, including 72 rational assignments, supplement
the coefficient proofs. Every supplied coordinate and every emitted gate reaches
the output; all final additions and positive-coordinate adapters are counted.

Replay from any working directory, for example `/`:

```sh
python3 /tmp/sandpile_shared_arithmetic35_36.py --repo /home/codex/.codex/worktrees/2a71/Proofs --expect /tmp/sandpile_shared_arithmetic35_36.json
python3 -O /tmp/sandpile_shared_arithmetic35_36.py --repo /home/codex/.codex/worktrees/2a71/Proofs --expect /tmp/sandpile_shared_arithmetic35_36.json
```

An external archive directory can be supplied with `--incoming` if the pinned
archives move. The receipt includes the helper's own SHA256. The assertions use
explicit exceptions and remain active under `-O`. Fresh normal and optimized
exact-receipt replays from `/` both passed. No archived source or historical
suite was executed.
