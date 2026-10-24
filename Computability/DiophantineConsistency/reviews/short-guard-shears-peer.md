# Peer review of the short guard and compact shears

The new guard and its three compact integer-coordinate translations appear
sound under the explicitly inherited native/Pell/refutation interfaces.
Independent exact algebra confirms the three claimed degrees and counts:

| Variant | Integer unknowns | Live binary operations | Exact degree |
|---|---:|---:|---:|
| Linear | 10 | 475 | 1179788 |
| Cubic | 10 | 478 | 1114252 |
| Six-term | 10 | 512 | 1080888 |

The generated circuits are compared with485,496,545-operation alternatives
at the corresponding degrees. All domains are unrestricted integers and all
twelve fixed leaves are the same coherent tuple. This is a comparison of
concrete evaluators, not a global optimality statement. No Lean was run.

## Positivity of cap is established before using the guard

This ordering matters. A statement about g*(cap-g) cannot itself justify
cap>0 on arbitrary integer inputs. The retained norm's initial square and
residue argument supplies that fact independently of the new guard.

The unchanged source congruences give b=Q=1 modulo3, gcd(b,Q)=1,
a0=1 modulo3 and a1=0 modulo3. The homogeneous quintic center is nonzero,
so a zero of the final norm has Sigma nonzero. For q=Z/Sigma, the norm
identity and a0!=a1 imply q!=0. The isolation identity makes each radicand a
rational square and therefore an integer square. This argument uses no
initial nonnegativity assumption on either radicand.

Put r=bQ. The factorization

```
a0=r*(1+(9*Delta-3)*r*z^2)
```

has coprime factors. A square product makes each factor a signed square;
r=1 modulo3 excludes a negative square. Thus r>0. Applying the same
argument to r=bQ gives b,Q>0, again using their residues. Hence
B=2^2134940*b^2>0 and cap=b*B^116>0 have been established before the guard.
Sigma nonzero also gives xi=x*z nonzero. If Delta<=0 the second factor of
a0 would be negative, contradicting the recovered positive factorization.
Thus Delta>0 is recovered in the required order.

For e=C-KL, the replacement is

```
Delta=g*(cap-g)*K^2-cap^2*e^2.
```

With cap>0 and Delta>0, one has K!=0 and g*(cap-g)>0, hence0<g<cap.
The identity4g(cap-g)=cap^2-(cap-2g)^2<=cap^2 gives4e^2<K^2. These are
the needed old soundness bounds, with a stronger upper bound on g. The
old and new guards are not asserted equivalent on all assignments.

## Canonical completeness and the top source coordinate

The actual raw source and weight table were read directly from the incoming
ZIP. The coordinate a has the unique maximum weight116. Source row4 is
exactly a-E-N*s-s, with no coefficient-port term. Every source coordinate
is positive, so a=E+(N+1)s>=3 on a source zero. Its packed offset therefore
gives g>=2*B^116, independently of the separate source coordinate named g.

The standard digit bound gives g<cap=b*B^116. Since B>b and B^116>=b^2,
one has g^3>=cap^2. The existing canonical approximation
|e|<|K|/(4g) and K!=0 now imply

```
Delta/K^2 > g*(cap-g)-cap^2/(16*g^2)
          >= g-g/16 > 0.
```

The integer cap-g is at least1. Thus no stronger interpolation or
approximation theorem is assumed. The Pell coefficient9*Delta-3 still
has3-adic valuation1, as required by the retained completion argument.
The new completeness proof concerns the canonical source witnesses, which
is the correct existential scope.

## The shears are actual polynomial automorphisms

For each variant, the actual old and new shear DAGs were normalized in the
five polynomial inputs h=halfA,B1,C,xi,y, imposing the exact A=2h identity.
This independently verifies all complete R polynomials, including the
26-monomial six-term polynomial, using integer coefficients in h. It does
not introduce division by A,C or xi or assume that a quotient happens to
be integral at selected points.

Dependency analysis confirms that every concrete R is independent of the
free integer m. Consequently m->m+R and m->m-R are inverse polynomial
maps on all integer tuples, including scale-zero cases. The candidate's
complete parent-gate substitution certificate proves its output is precisely
P_short_guard(v,m+R(v)). The independent old/new R checks confirm the cut
identifications and not only a numerical substitution sample.

For robustness in later generalizations, explicitly checking m-independence
inside the main generator would make this essential hypothesis visible
there too. It holds for every current circuit. No correctness issue was
found in the generated substitutions.

## Exact degree with the actual fixed leading prefix

Sparse normalization of the literal parent source registers at the base
atom confirms kernel heads -6*B^1408,2*B^1727,B^1636 and ell head B^116.
These heads contain no opaque coefficient leaf. The actual radix and
threshold payloads are the positive powers2^2134940 and2^34159017.
Therefore the prefix has nonzero leading terms

```
X ~ 2*B^3971,       Y=2^34159017*b*B^2109,
deg(X)=7942,        deg(Y)=4219,
deg(cap)=233,       deg(g)=2,
deg(L)=4220,        deg(K)=28548,
deg(A)=16384,       deg(r)=114189.
```

The two pieces of the new Delta have degrees57331 and66002, respectively.
The negative second piece is uniquely largest. Hence deg(Delta)=66002 and

```
deg(a0)=66002+2*(114189+1)=294382.
```

This explains the exact237-degree drop from the old a0 degree294619.
All leading factors are nonzero polynomials for the actual fixed tuple.

The original full radical/defect certificate was authenticated directly
from `ConZFC_Polynomial_Shears_2026-10-23.zip`. An independent SymPy Poly
calculation over Z reconstructs a1 and verifies its identities with the
actual R0,R1,R6. At weights(16384,7942,1,2,1) for h,B1,C,xi,y, the complete
unique defect heads are

| Variant | Defect degree | Unique leading monomial of a1-R^2 |
|---|---:|---|
| Linear | 426050 | -17592186044416*h^26*C^40*xi^12*y^2 |
| Cubic | 393282 | 13194139533312*h^24*C^40*xi^12*y^2 |
| Six-term | 368449 | 6803228196864*h^22*B1*C^36*xi^11*y |

All R have degree229409, a1 has degree458818, Sigma has degree81922, and
Theta has degree81925. Writing Z=Sigma*m-Theta and delta1=a1-R^2, the
translated norm is

```
[Z^2+2*Sigma*R*Z-Sigma^2*(a0+delta1)]^2
 -4*Sigma^4*a0*a1.
```

The squared inner degrees are1179788,1114252,1064586. The cross term's
exact degree is4*81922+294382+458818=1080888. Each comparison has a unique
dominant piece, so the three final degrees are exactly1179788,1114252 and
1080888. The unique weighted heads and actual nonzero prefix imply
attainment over Z; modular degree guesses are not needed for this conclusion.

## Replays and limits

The peer receipt is `short-guard-shears-peer.json`. It records all unique
heads, actual source hashes, maximum-weight row, m-independence and counts.
Both normal and optimized runs of the candidate's `--check` pass. The new
ZIP and earlier immutable shear ZIP were independently authenticated, and
all retained source members were compared with their raw archive bytes.

These checks and the new ordinary guard proof preserve the parent's
existential consistency interpretation. They do not reprove the retained
native/compiler and syntactic-refutation calibration or export an internal
object-ZFC derivation. Formalization remains paused.
