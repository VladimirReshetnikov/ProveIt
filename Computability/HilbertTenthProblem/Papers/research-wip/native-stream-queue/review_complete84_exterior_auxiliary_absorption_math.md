# Independent mathematical review of exterior auxiliary absorption

**PASS, with no remaining mathematical finding.** The revised
[author theorem](complete84_exterior_auxiliary_absorption.md) proves a finite
ordinary-input projection only for the nonzero sector of a fixed polynomial
substitution for the auxiliary witness i. It correctly leaves the zero sector
separate. It is not an arithmetic improvement or a lower bound for arbitrary
complete circuits.

## Frozen files and read scope

| Author file | SHA-256 |
|---|---|
| `complete84_exterior_auxiliary_absorption.py` | `46e42d8947c1e5cbed62a4473fa83d96115a80b334656ea45ad1f31796bde0a9` |
| `complete84_exterior_auxiliary_absorption.json` | `ec0b2a298d4382867ca0d638e3b52b18be3ad38a64ea7c4efb96d1ad985d692b` |
| `complete84_exterior_auxiliary_absorption.md` | `69f8e40bd44dca5bcb2f0f292a2ad842fff5a41b2014007f3f986176cd7bd8de` |

I read the complete author note, its census and symbolic-check implementation,
and the receipt's theorem, source census, factor identities and full unchanged
84-row array. I authenticated all twelve predecessor pins listed in that
receipt and compared its saved array with the actual pinned complete84 JSON.
No author or predecessor helper was executed or imported for this review.
The receipt's numerical component tables are supplementary author evidence,
not independent numerical tests claimed here.

The mathematical dependency reads were complete84 Sections 1–3; the
normalized85 mathematical review Sections 1–6; the input-quotient dichotomy
Sections 2–5; computed-gamma Sections 2–3; direct supplied-gamma Sections 2–4;
the half-binomial compiler Sections 1–4; complete76 Section 1; and complete78
Section 2 through equation (8), with the adjacent coefficient-bound context.
These reads check the relevant native and compiler hypotheses rather than
recertifying every predecessor construction or historical program.

The immediate complete84 JSON pin is
`8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`.
The normalized85 proof pin is
`77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d`;
the input-dichotomy proof pin is
`46d6457d10d1847cd4241aa1ed6705bf520216fc32cf97891c1f439f6c2c2505`.
The other nine authenticated pins remain explicitly recorded in the frozen
author receipt.

## Independent mathematical checks

**Every auxiliary completion.** At a positive parent zero, cancellation of
positive Delta restores the normalized85 equation, including
`f²−Delta*(i*c²)²=1`. Its Pell index m satisfies `psi(m)=i*c²`.
The native main index is R and `c=psi(R)>2`. Strong divisibility gives R|m;
writing m=Rj and expanding the Pell unit gives

    psi(Rj)/c = j*D^(j−1) modulo c.

Since gcd(D,c)=1 and the left side is divisible by c, c|j. Thus Rc|m
for every positive completion, without selecting a canonical auxiliary
index. The addition formula and D>c imply `psi(jR)>c^j` for j>=2.
Therefore `i>=psi(Rc)/c²>c^(c−2)`. None of this requires the auxiliary
quotient or its Pell index to be bounded.

**All 85 exterior arguments.** The displayed census excludes the whole
syntactic dependency cone of i,f,T,y_aux, leaving 64 computed values and
21 exterior free values (fourteen witnesses, x and six fixed numerals).
At parent zeros, gamma=rho+sigma>rho selects the canonical input branch
of the pinned dichotomy. Thus kappa<c, mu<D, W=2^u>0 and
`delta,rho,sigma<c`; these input bounds would not hold for arbitrary
independent-gamma completions.

The elementary starting estimate
`c>=psi(3)=4(a+2)²−1` gives `a²<c/4`, Delta<c and H<c.
For the first-root block, U=XY²<a² and k<c imply
`kU<c²/4`, `k(U+1)<c²/2`, and hence its product plus one is below c⁴.
The main root obeys `D<(a+2)c<c²`. The input root's positive summands
are smaller than mu<D, so their squares and the scaled coefficient square
are below c⁴. Unit rows are one.

I also checked the less immediate fixed-coefficient bounds. The modified
mask export is MF_source=MF_native+B−1, with MF_native<B−1; the shifted
source MF must not be given the smaller native bound. The optional high
DC monomial remains below the enlarged cell width and its coefficients
below the strengthened inner radix, so `DC,DR<B` and
`Kconstant=DC+B*DR<B²<=q²` are valid inherited recipe bounds.
Together with C<q, w=X/q and Y>=q³, these give

    (Kconstant+w)C < q³+X,
    transport_partial < q³+X+q < a.

The packing masks are below 3q³<a. The remaining fixed ports use b<=d
and `2d<B<=q`, while `2dx<q` bounds the ordinary input. This covers the
fixed numerals as well as witnesses and computed fields. The sole prose
correction from the initially reviewed note was the remaining-exterior
table's strict bound: its R12 entry equals a. The final wording says
“at most a, with R12=a”; the strict overall c⁴ bound was unaffected.

**Signed polynomial and effective threshold.** The actual source has i
only in `aux_coefficient_root=i*Ac2`, whose only consumer squares it.
Every exterior argument is independent of all four auxiliary witnesses.
Consequently a substituted zero with nonzero signed G maps to an actual
positive parent zero by setting i=|G|, with every other supplied coordinate
and every exterior argument unchanged. This map precedes use of the
parent bounds; it does not assume positivity of G on the whole domain.

For a fixed integer polynomial of total degree t and coefficient norm
L=max(1,sum|coefficients|), the 85 bounds give `|G|<=L*c^(4t)` even
when the named arguments are dependent or repeated. With
`s=ceil(log2 L)`, the assumption `c>=4t+3+s` makes
`c^(c−2−4t)>=2^(s+1)>L`, contradicting the strict auxiliary lower bound.
Thus `c<=4t+2+s`, and `2dx+b<R<c` proves the finite ordinary-input bound.
Fixed compiler-dependent coefficients are allowed; witness- or input-dependent
exponents are not fixed polynomials in this argument.

**Exact zero sector.** The full source at i=0 is precisely

    Delta*(P5*f²*y_aux²−1).

Delta is positive already from positive exterior X,Y, before any norm
or rank theorem. Integer P5 and positive integer f,y_aux then force
`P5=1` and `f=y_aux=1`; conversely these conditions, together with G=0,
make the full polynomial zero for every positive T. The independence of
G's arguments from T is essential and holds by the chosen census.
No native decoding or finite-input statement is inferred for this sector.

## Boundary of this conclusion

The nonzero-sector exclusion is a statement about the literal complete84
substitution i=G in this particular exterior interface. It does not cover
auxiliary-dependent expressions, divisions, changed norm equations,
free-coefficient replacements, or new circuit representations. An unbounded
input projection of such a substituted source must arise in its G=0 sector;
the theorem does not certify that sector as a useful universal language.
The full84 operation count and the separate unresolved independent-gamma83
question remain unchanged.
