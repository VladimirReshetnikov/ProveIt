# One paid addition removed from the complete factored counter step

The complete scalar counter-program graph in
`residue_affine_factored_counter_step.md` admits a one-addition saving with
the same six positive witnesses, five equations and five table interpolants.
The new counts are

    graph:      10B+7  = (5B+1)M + (5B+6)A,
    polynomial: 10B+21 = (5B+6)M + (5B+15)A.

For the actual saved B=14 fixture this gives 147 operations for the five
equalities and a complete 161-operation polynomial, with exact degree28.
The old counts were148 and162. All control lookup and both modular guards
remain charged. This is a uniform one-step compiler for the same scalar
counter substrate; the prime-power ordinary-input loader and an unbounded
history certificate are not supplied by this improvement.

## 1. All-program contract and exact replacement

Fix a finite deterministic counter program with INC and conditional DEC
instructions, as in the parent. Its K positive control labels are filled
with instructions, every target lies in1,...,K, the designated register
primes are distinct, and each is coprime to K. The parent acceptance cleanup
and totalization may be used unchanged. Split each INC into one branch and
each conditional DEC into a decrement and a zero branch, for B branches.
For branch z record source I, target O, active prime p and

| Branch | A | D | Legal payload condition |
|---|---:|---:|---|
| INC | p | 1 | always |
| DEC | 1 | p | p divides P |
| ZERO | 1 | 1 | p does not divide P |

Put `E=A(K-I)-D(K-O)`. Interpolate I,A,D,E,p at1,...,B with a common
positive denominator L, obtaining the five integer-coefficient polynomials
IT,AT,DT,ET,PT with values L times the entries. Every degree-(B-1) Horner
schedule is padded and fully paid. Let `S=AT+DT`, `H=PT+L-S`.

At strictly positive integer endpoints n,y, supply exactly the positive
integers z,v,P,Q,U,V and impose

    z+v = B+1,
    L*n+L*K = L*K*P+IT,
    DT*y = AT*n+ET,
    H*P+S+V-2L = PT*Q,
    U+V = PT.                                           (1)

Only the fourth equation changes. The old fourth residual and the retained
fifth residual, with left-minus-right signs, were

    g_old = H*P+S+PT-2L-PT*Q-U,
    c     = U+V-PT.

The new fourth residual is `g_new=g_old+c`. This is an invertible elementary
change of the five residuals, so their common zero tuples are identical
over every commutative ring. In particular, all old positive witnesses
are retained without a coordinate transformation or new sign assumption.
The two SOS polynomials are different off that common locus. Their exact
all-ring identity is

    F_new-F_old = 2*g_old*c+c^2.                         (2)

The common real, hence positive integer, zero set follows because a sum
of squares is zero exactly when its individual real residuals are zero.
No corresponding claim about arbitrary complex SOS zero sets is made.

## 2. Complete scalar soundness and completeness

The first equation confines z to the finite branch table. The input
equation gives `n=K(P-1)+I`, uniquely identifying the current control and
positive payload. The output equation gives `D*y=A*n+E`.

At the selected row write `h=p+1-A-D` and `Z=hP+A+D-2`. The last two
equations of(1) become

    L*Z+V = L*p*Q,       U+V = L*p.

Thus `L*Z=L*p*(Q-1)+U`, and divisibility forces L to divide U and V.
Their strict positivity yields `1<=U/L<=p-1`. Hence these equations are
equivalent to a nonzero remainder for Z modulo p, with the positive
quotient shifted by one. On INC and DEC, h=0 and Z=p-1, so this test
always passes. On ZERO, Z=(p-1)P, and p is prime, so it passes exactly
when p does not divide P.

On DEC the separate output equation is
`p*(y+K-O)=K*P`. Coprimality forces p to divide P and gives the correct
positive successor `y=K(P/p-1)+O`. On INC it gives
`y=K(pP-1)+O`; on ZERO it gives `y=K(P-1)+O`. Thus a false decrement
or zero branch cannot survive by choosing a different positive y.

Conversely, for a genuine step choose its table row and `v=B+1-z`.
Its Z is positive and has remainder R in1,...,p-1. Set
`Q=floor(Z/p)+1`, `U=L*R`, `V=L*(p-R)`. These six positive witnesses
satisfy every equation in(1). This includes payload P=1. Arbitrary positive
n may encode payloads with undesignated prime factors; the same total
divisibility map is used on those values, exactly as in the parent.

The parent's universal-substrate simulation on prime-supported inputs is
therefore preserved whenever that already established program is selected.
The saved small fixture is not universal. Neither its numerical checks nor
this local theorem pays `K*(2^e*3^x-1)+j_start`, a duration, synchronization,
or final acceptance in a fixed-arity universal polynomial.

## 3. Complete schedules and degree

The five interpolants cost `5(B-1)M+5(B-1)A`. The remaining graph ledger is

| Block | M | A |
|---|---:|---:|
| Selector z+v | 0 | 1 |
| Input/control sides | 2 | 2 |
| Output sides | 2 | 1 |
| S,H; new guard sides; U+V | 2 | 7 |
| Total after interpolation | 6 | 11 |

The guard schedule is literal:

    S=AT+DT; pL=PT+L; H=pL-S;
    HP=H*P; a=HP+S; b=a+V; guard_lhs=b-2L;
    guard_rhs=PT*Q; complement=U+V.

It uses2M+7A including S,H and the complement. The old corresponding
block uses2M+8A. Forming all five left-minus-right residuals, their squares,
and four joins adds5M+9A. Fixed multiplications by L and LK are paid;
fixed numerals, including2L andLK, use the parent's same constant convention.

Every residual has degree at most B (or one when B=1), giving SOS degree
at most2B. The saved B=14 source has exact degree28: the leading coefficient
of H as a degree13 polynomial in z is5447, so its guard contains
`5447*z^13*P`; no other residual contains this monomial. Its square supplies
a nonzero degree28 leader. General programs can have lower actual degree.

## 4. What this does and does not transfer from positive guards

The Markov observation motivated checking already constrained expressions.
This scalar saving does not remove the nonzero-remainder test; it shares
the retained complement equation through an invertible residual change.
In particular, setting p=A+D-1 is invalid on ZERO: it would set p=1 and
make its two positive scaled remainder complements impossible.

A rowwise information obstruction is also explicit. Take K=5 and a ZERO
row with I=O=1, A=D=1, E=0. Active prime2 versus3 gives the same four
entries I,A,D,E but opposite zero-branch legality at payload P=2 (n=y=6).
Therefore these four entries alone do not determine the active-prime guard.
This does not prove that a whole program's four interpolants cannot admit
a specialized shared lookup: other rows can carry additional information.
Replacing PT by H is merely a five-column reparametrization unless those
extra computations are exhibited and charged.

A separate vector-coordinate guard theorem is recorded in
`counter_vector_positive_guard.md`. Its endpoint interface differs, so it
is not used to subtract costs from this scalar source.

## 5. Fresh complete source and exact scope

The new standard-library helper independently constructs the old fixture
table by Newton forward differences. All70 values and all five coefficient
rows match the inert parent receipt, with L=6227020800. It emits the full
147-row side-computation source and its complete161-row SOS extension.
All eight supplied ports and every row are structurally live. A fresh
sparse expansion of the new array checks all five displayed residuals,
the complete output, exact degree28 and the all-ring correction(2).
It tests110 true and4510 false branch/output cases using only this newly
authored source. The all-program result is proved in Sections1–3, rather
than extrapolated from that nonuniversal fixture.

The parent Markdown and helper source were read in full as inert text;
the parent receipt was read as data. No parent source array, helper,
archived program, builder or copied predecessor was run or imported.
Only newly authored code ran before freeze, from `/`. Fresh normal and
optimized runs passed and produced byte-identical receipts. No repository
or Git mutation occurred. No minimum-cost claim is made.

| Inert dependency | SHA-256 |
|---|---|
| `residue_affine_factored_counter_step.md` | `60250f0f6d12f7583b5de747c82d0d91205eab98ca0f4095992d458aaf8a951f` |
| `residue_affine_factored_counter_step.py` | `0dcc6e5d4cf306037d343d7aaed8183f920c2b9e15e1b31757aadcf4606feb8a` |
| `residue_affine_factored_counter_step.json` | `fc8c20c02a28edcb6eaa3eed27128e282ea3835c88fc313d907c91e6e733b282` |
| `markov_positive_guard_savings.md` | `901accac868c13967883c56ff5b5a949ef42fcfd82a470999f042272ead8dc15` |

New helper SHA-256:
`810a9e2572d2efd075dcfcd7d5e024a90ad3d4c4aac588d3adc9860be935871d`.
New receipt SHA-256:
`3809b7765209043c3de7afbdc7188b237b4a68b9162f59ddc34ece91262d7673`.
