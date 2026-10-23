# A 5,263-tile coefficient backend with B = 2^(5^16)

## Statement and provenance

This construction replaces all four fixed integer coefficient ports of the
inputless native-window/Pell compiler together. Its local language is a subset
of package 11's T4 language, with its same globally impossible forbidden tile
retained. The local language and scalar layout are new. The general compiler,
Pell extraction, actual-rank tuning, and K215 endpoint are inherited mathematical
theorems, not newly kernel-formalized results of this note.

The source snapshot is ProveIt
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`. The direct parent is
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/11-t4/bridge/BRIDGE_AUDIT.md`.
The original arithmetic interface is the six-equation inputless system of
wave-1 package 06, retained within package 11. Any subsequent algebraic
construction proved equivalent to this interface may use the new tuple. No
port from a different coefficient recipe may be mixed into the tuple below.

All unknowns in those arithmetic equations remain unchanged. The powers in
this note define fixed finite integer coefficients; none has an unknown
exponent. Therefore this does not replace a polynomial equation by an
exponential Diophantine equation.

## 1. Local language

Use exactly the 439 T4 cell symbols and original completed K215 transition
function. Codes 0 and 1 are headless tape symbols. Code 2(q+1)+b denotes bit b
with state q, for 0 <= q <= 215. State 215 is absorbing only after the literal
halting transition has completed its write and movement. Set

    L=434, Q=435, R=436, V=437, H=438.

The initialization payloads are blank, with a state-0 head at Q only.
The four coordinates of a tile are (left,center,right,next).

Start is S=(434,435,436,1). Retain E=(438,0,0,438) as the forbidden tile.
Apart from E, admit precisely the tiles satisfying the original T4 predicate
and the following additional requirements:

1. Each adjacent horizontal pair, (left,center) and (center,right), satisfies
   the following pair predicate. Two V symbols are forbidden. Immediately
   right of V an initialization phase must be L; immediately left of V it
   must be R. If neither member is V, they agree on being H, agree on being an
   initialization phase, and, when phases, form one of LL,LQ,QR,RR.
2. If V occurs in the horizontal triple, every ordinary symbol in that triple
   is the blank headless symbol 0 and Q is absent. Thus every ordinary cell
   within distance two of a vertical boundary is blank and headless.
3. If next=H, every head in the horizontal triple is halted (state 215).

The original one-head restriction is retained. Enumerate S first, E second,
and all other admitted tiles in lexicographic order. This is a bounded
computation independent of whether K215 halts.

### Soundness

Every new tile is an old T4 tile. The only exempted tile E was already an old
T4 tile. Therefore a new globally valid marked plane is an old valid marked
plane, and the inherited soundness theorem yields a finite blank K215 halt.
For completeness of the coefficient semantics, E remains globally impossible:
its left neighbor would have center H and right symbol 0. Such a tile is not
E, because E has center 0, and its horizontal pair fails the new predicate.

### Completeness, including helical seams

Given a finite blank K215 halt, retain its true finite history and choose
blank margins with at least two untouched headless tape cells between every
visited head position and each vertical boundary. The ordinary canonical
periodic tableau has a full H row, then a phase row L^u Q R^v, followed by the
deterministic computation and an arbitrarily long absorbing halted tail.
Every new horizontal pair condition holds on each row. Whenever next=H the
preceding row is halted throughout its strip, so requirement 3 holds. The
blank margins give requirement 2.

The inherited helical presentation offsets the time coordinate by one upon
crossing each vertical seam. All cells within distance two of such a seam
are either blank headless cells, their boundary-adjacent phase L or R, or H.
Thus the two sides may be at different times without violating any new
condition; the boundary symbol V separates those sides. There are still
arbitrarily large independent choices of width and height, including powers
of five. The canonical cyclic presentation contains exactly one Start and no
E. Soundness does not assume uniqueness of Start in arbitrary solutions.

### Exact count, independently of running the enumerator

For an ordinary headless center, each neighboring nonboundary cell is one of
the two ordinary headless symbols or the 432 ordinary headed symbols, with
at most one head. This gives 4+2*432*2=1732 normal successor tiles. For
next=H only the two halted headed symbols are permitted, giving
4+2*2*2=12 terminal tiles. Center 0 additionally has the three boundary
neighborhoods (V,0,0),(0,0,V),(V,0,V), each with both a normal successor and H.
The deliberately retained E contributes one further center-0 tile.

Each of the 430 working-head center symbols has four choices of its two
headless neighbors and one successor, giving 1720 tiles. Each of the two
halt-head center symbols has four normal and four H successors, giving 16.
The two initialization headless symbols L and R each have three normal and
two H cases; Q has just Start. A V center has three possibilities independently
on either side, yielding nine cases. An H center has two boundary choices on
either side and three phase successors, yielding twelve cases. Hence

    1751 + 1744 + 1720 + 16 + 5 + 5 + 1 + 9 + 12 = 5263.

The separate exhaustive program checks all 5215 permitted horizontal triples
against all 439 successors (2,289,385 cases), then adds E and fixes the ordering.
The compact JSON list has SHA-256
`40044724fa9e33d8352b7185769d63a960f28e94270ea3925fa74220ec45e7ec`.

## 2. Exact coefficient recipe

Set

    a0=439, k=5263, ell=13, A=8192, p=1080, m=7023,
    b=78125=5^7, Lcell=1953125=5^9, d=b*Lcell=152587890625=5^16,
    rho=2^b, B=rho^Lcell=2^d,
    M=7021, Emax=189567, Hc=359389, T1=738963, T2=1118101.

For 0 <= u <= 438, put

    e_left(u)=6580+u, e_center(u)=6141+u,
    e_right(u)=5702+u, e_next(u)=5263+u.

Let the support Eset consist of selectors 0,...,5262, those four copy
intervals, dummy position 7019, and anchors M,3M,9M,27M. It has 7024 elements.
The extra upper dummy position is 7020, strictly below the first anchor M.
Define

    mu = A-2 + sum(A^j, j=1,...,2840).

For the ith tile w_i=(l_i,c_i,r_i,n_i), put

    v_i = 1 + A^(1+l_i) + A^(440+c_i) + A^(879+r_i)
            + A^(1318+n_i) + sum(A^(1756+t), t=1,...,4).

At the copy positions define

    v_e_left(u)=A^(1+u), v_e_center(u)=A^(440+u),
    v_e_right(u)=A^(879+u), v_e_next(u)=A^(1318+u).

At anchor 3^(t-1)M put v=A^(1756+t), for t=1,...,4; the dummy coefficient is 0.
Now define four unshifted integers:

    DC = rho^878 + rho^359828 + rho^56168 + rho^168504
         + sum(v_e*(rho^(T1-e)+rho^(T2-e)), e in Eset),
    DR = rho^359389,
    MF0 = mu*(rho^T1+rho^T2)
          + sum(rho^(6141+u),u=0,...,438)
          + sum(rho^(359389+6580+u)+rho^(359389+6141+u),u=0,...,438)
          + rho^63189 + rho^189567,
    MC = B-1 - sum(rho^e,e in Eset except e=1) - 2*rho^7019,
    MF_native = MF0+4.

The four final ports are, inseparably,

    beta=B-1, K=DC+B*DR, MC, MF_source=MF_native+B-1.

The last port is the shifted high mask, as required by the inputless equations.
The use of exponent 878 rather than the old 1317 is intentional: the next
copy is now two alphabet intervals below the center copy.

## 3. Compiler geometry and arithmetic

### Clause fields and carry bound

The original clause coefficients and A-radix clause tests are unchanged except
for tile contents and alphabet size k. A=8192 exceeds k+1. There are still
four symbol-copy groups and four anchors. We have

    m=2*ell+11*a0+8+2*p=7023,
    pc(mu)=ell-1+2840=2852,
    pc(MF_native)=2*2852+3*439+2+1=7024,
    pc(MC)=d-7024.

No terms in these population sums overlap: the two mu bands, the three
overlap groups, the two anchor targets, and bit 2 are distinct. At MC, the
omitted selector-1 position is restored, while the upper dummy bit is removed,
so its zero population is exactly 7024. In particular

    MC=2 (mod4), MF_native=4 (mod8),
    0 < MC,MF_native < B-1, pc(MC)+pc(MF_native)=d.

The exact original sufficient bound is

    bmin=max(ell*(4*a0+5+p)+3,
      ell*(4*a0+4)+bitlength(4*(m+3)*(18*(k+4*a0+4)+6)+8)+1,4)=36936.

Our b=78125 exceeds it. The independent exact integer mass calculation gives
bitlength(mu)=36921 and
bitlength(4*(7024+2)*(2*sum(v_e)+6)+8)=22909.
Thus rho exceeds both 2*mu+4 and the required carry threshold. The original
binary-rotation carry argument applies, including the optional upper dummy bit.

### Exact overlap fields

At center-copy target e_center(u), the bare shift 878=2*a0 has exactly the
source e_next(u). At Hc+e_left(u) and Hc+e_center(u), the bare shift Hc+a0 has
sources e_center(u) and e_right(u), while DR has respectively sources
e_left(u) and e_center(u). The other bare shifts 8M and 24M have exactly the
anchor source/target pairs (M,9M) and (3M,27M). All other hits at these 1319
targets are absent, as verified by exact finite set arithmetic.

Every target is below T1-Emax. At each Tj there is no bare contribution and
the other clause band cannot contribute. Thus the clause sums and the three
overlap identities have exactly their original meanings:

    w_i.right = w_(i-1).center,
    w_i.center = w_(i-1).left,
    w_i.next = w_(i-h).center.

These imply w_i=(a_(i+1),a_i,a_(i-1),a_(i-h)) for the central word a_i, for any
cyclic temporal stride h, including colliding residues. The resulting plane
has the same finite-strip soundness argument as the original compiler.

### All rotations, not just the unrotated case

All support and upper-dummy positions are in [0,Emax], and

    T2-T1 = 379138 = 2*Emax+4,
    T2+2*Emax+2 = 1497237 < Lcell.

The two possible clause-band contamination sets are therefore disjoint modulo
Lcell. The carry bound and two anchor parity tests force a binary rotation to
be radix-aligned, exactly as in the original argument. The only support pair
with difference 18M is (9M,27M): nonanchor support lies below M, and the other
anchor differences do not equal 18M. The circumference exceeds twice the
support diameter, so no additional modular pair occurs. The two anchor tests
therefore force a radix rotation of 0 modulo Lcell. This is the required
whole-cell temporal alignment, not a restriction on the integer stride.

### Actual-rank tuning and the changed unit

Since b is a power of five, rho=2 modulo5. The difference T2-T1 is 2 modulo4,
so paired clause contributions cancel modulo5 for every coefficient v_e.
The four bare exponents reduce modulo4 to 2,0,0,0, respectively. Consequently

    DC=2 (mod5), DR=2 (mod5), 2*DC-DR=2 (mod5).

The old value 3 is not required by the tuning proof; being a unit modulo5 is
the entire requirement. More explicitly, for w,H powers of five and N=wH,
we have B=2, B^w=2, q=B^N=2 modulo5. The bracket in the exact dummy increment

    Gamma = rho^7019*(q^2-1)*[1+q*(DC+B*DR+B^w)]

is therefore

    1+2*(DC+2*DR+2) = 2*DC-DR = 2 (mod5).

Also rho^7019=3 and q^2-1=3 modulo5, so Gamma=3 modulo5. Thus Gamma is a unit
modulo the full modulus dN, which is a power of five. Turning on a low dummy
bit in cell j changes the actual packed index by -Gamma*B^j, with the same
no-wrap conditions j+1,j+w<N. The unchanged Boolean subset adjustment on
the cell set {4j:0<=j<N/5} union {1} supplies the target index congruence
R=d*w modulo dN. Arbitrarily large power-of-five widths and heights supply
H>=25 and N>25d. No independently selectable rank is being substituted for
the packed index, and no residue condition has been lost.

Start is still selector 0 and E still selector 1. The canonical origin test
depends on the unit selector contribution at Start, and every copy/dummy
position is positive. Hence its original argument is unaffected by compacting
the copy intervals. The low mask congruences, odd d, and canonical index
congruence R=3 modulo4 are unchanged. Those properties support later odd-index
or square-parameter specializations as well as the original positive system.

## 4. Size and verification scope

The old best T4 recipe used B=2^(5^18); the new B=2^(5^16). Therefore beta has
exactly 25 times fewer bits: 152,587,890,625 bits, about 19.1 decimal GB when
stored as binary. K is the largest port, with 180,665,156,251 bits. None of
these final giant integers is expanded; their finite recipes are exact.

The program verifies the complete finite alphabet, its inclusion in the old
alphabet, global impossibility of E through all possible adjacent tiles,
population/carry data, every convolution target, the all-rotation support
intersections, the five-adic unit, and 18 toy halting tableaux with 927 windows.
The toy controls alter specified transitions solely to create finite examples;
they make no statement about whether literal K215 halts. The universal proof
is the argument above combined with the inherited mathematical compiler and
Pell theorems. No new end-to-end Lean/Rocq proof or encoded internal ZFC
derivation is claimed.

## 5. Logical endpoint audit

At the pinned commit, KEndpoint215.lean states the unconditional theorem

    BlankHalts machine215 <-> BProv ZFCax_s [] Form.fBot.

There is no consistency, transitive-model, or standard-model premise. The
repository verification README records Lean's endpoint axioms as only
propext, Classical.choice, Quot.sound, and Rocq's dense and sparse theorem
pairs as closed under the global context. Those are repository build records,
not freshly replayed builds in this package. The ordinary K215 proof explicitly
states that its exact halting/refutation equivalence is formalizable in ZFC;
an internal PA endpoint is separately marked open. The combined mathematical
conclusion here is therefore ZFC-provable equivalence of solvability with a
finite ZFC refutation, and equivalence of unsolvability with Con(ZFC), using
the inherited ordinary mathematical calibration. This is not a proof of
Con(ZFC) or of unsolvability itself.

