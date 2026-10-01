# A computed positive checksum field removes one multiplication

After [computing both native input fields](group_projective_computed_input_fields.md),
the same packed radix region also makes a computed F0 strictly positive.
Choosing the checksum-one branch lets the source reuse its three checksum
additions to define F0 and delete the multiplication by the checksum unit.
This saves **one multiplication and one positive witness**, with unchanged
comparison count, and lowers the exact degree.

The earlier coupled-linear proof already normalizes every negative-checksum
zero to a positive-checksum zero at the same ordinary input and outer
history. Therefore restricting to checksum one preserves the accepted
input relation. It is not coordinate erasure on every parent tuple.

Use the fixed compiler parameters and notation

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1,
    nu=1+chi.

Both mask options retain their original hypotheses, including m>=8
for epsilon=1. Fixed positive alpha,beta satisfy `alpha+beta+1>=m`.
The complete successor ledger is

| Earlier native field variant; now all Fi computed | Certificate | Equations | Positive witnesses | SOS polynomial | Exact degree |
|---|---:|---:|---:|---:|---:|
|four: a,d,k,s|C+3|12-chi|m+30-chi|C+38-3chi|22nu L+54|
|six: a,c,d,k,r,s|C+3|10-chi|m+28-chi|C+32-3chi|nu(38L+2m+30)+60|

The illustrative ten-letter table, six-field variant and both optional
projections give **261 certificate operations, 9 equations, 43 positive
witnesses and a 287-operation polynomial of exact degree 3376**. Without
controller-mask reuse the figures are **262/288 operations and degree
2768**, with the same equation and witness counts. These remain complete
fixed-table formulas, not numerical bounds for an instantiated universal
alphabet. The separate 75/88 frontiers are unchanged.

## 1. The checksum-one field is positive before native typing

The previous packet proves, using only the retained raw edge checksum,
repunit and joint scalar bound,

    B=16D>=64, P>=B, J>=1,
    0<=Z<T2, H>=B*T2, M>=(B-1)*T2,
    T=P^(m+8), T2=P^(L-2), N=T2*P^2.             (1)

No native norm, recovered sign, Boolean cell or dyadic scale is needed
for these statements. In particular its fields

    F1=16(H-Z)+4, F2=16(M-Z)+2, F3=16Z+8          (2)

are already positive.

We also need the upper bounds on the two lower bodies. In the previous
notation,

    Hbody=Hb+P^8*Hc+T*Hb,
    Mbody=Mb+P^8*Mc+T*Rb.

The first terms of both bodies are less than T. The range width ell_r
is eight or m, with ell_r>=8. Its mask is

    Rb=(2D-1)J*sum_(i=0)^(ell_r-1) P^i.

Since `(2D-1)J<(B-1)J=P-1`, every coefficient is below P, so
Rb<P^ell_r and T2=T*P^ell_r. Also Hb<P^8<=P^ell_r. Therefore

    0<=Hbody<T2, 0<=Mbody<T2.                     (3)

The joined inputs are H=Hbody+B*T2 and M=Mbody+(B-1)*T2. As Z>=0,

    H+M-Z<(2B+1)*T2<P^2*T2=N.                   (4)

The second inequality follows from P>=B>=64. All quantities are
integers, so `N-H-M+Z>=1`. Consequently

    F0=q-F1-F2-F3-1
      =16(N-H-M+Z)-15>=1, q=16N.                 (5)

This supplies strict positivity and the residue F0=1 mod16 before
any native argument. The whole quartet now has positive computed
values. As in the previous projection, the retained outer bounds
remain part of the certificate; positivity is not asserted on arbitrary
off-zero supplied assignments.

## 2. Three existing additions define F0

The previous literal source has, after its input-port substitutions,

    shared_sum02=F0+F2,
    bs_Q=shared_sum02+padded_A,
    Q=q-bs_Q,
    unit_product=unit_pair*Q,

where padded_A=F1+F3 and unit_pair=N1*N3. Replace the three additions
in topological order by

    bs_Q=q-padded_A,
    shared_sum02=bs_Q-1,
    computed_F0=shared_sum02-F2.                 (6)

Alias supplied F0 to computed_F0, old Q to the fixed numeral one, and
unit_product to unit_pair. Delete the unit_product multiplication and
the supplied F0 coordinate. The actual source redirects every consumer;
the packed native index is recomputed with (6), and the five remaining
norm/index/linear factors keep their paid multiplication chain.
No comparison disappears, because Q was already a factor in the unit
comparison rather than a separate equation.

The [checker](group_projective_computed_checksum_field.py) verifies the
old gate patterns before rewriting and checks a topological schedule.
Its `rewrite(old_packet)` exposes this local transformation for later
composition. The three defining additions were already paid; the
certificate and SOS each save exactly one multiplication. All other
fixed-numeral and residual arithmetic stays charged.

For arbitrary integer supplied assignments, restore parent F0 using
(6). Then its Q is identically one. Every comparison and the full SOS
are identical to the new source after aliasing. This exact off-zero
identity is distinct from the positive input-equivalence argument below.

## 3. Normalize before restricting the checksum branch

At a new positive zero, the retained outer bounds imply (1)-(5).
Restore the strictly positive F0. The previous source's checksum is
one, all its other residuals agree, and its other supplied witnesses
are unchanged. This is a positive parent zero at the same input.

Conversely, take any positive zero of the complete two-field parent.
Its coupled sign theorem recovers

    N0=N1=N3=Nl=1, Q=Nk=epsilon_k in {-1,1}.

If epsilon_k=1, the old F0 is already exactly (5), and erasing it
gives a new positive zero. If epsilon_k=-1, first apply the proved
positive normalization

    F0'=F0-2, r'=r-2,
    bound_beta'=bound_beta+2.                    (7)

The port residues give F0=3 mod16, so F0'>0. The four-field variant
changes supplied r explicitly; the six-field variant recomputes it
from the packed quartet. No outer history, selected output, edge field,
input x or fixed compiler numeral changes. In particular the two
already computed fields F1,F2 depend only on those unchanged outer
quantities, so their definitions remain identical. The coupled proof
restores every native comparison and gives Q'=Nk'=1.

Now erase F0'. Since Q'=1, its value is precisely the expression (5).
The resulting supplied coordinates are positive and all new residuals
vanish. These two directions establish exactly the same accepted inputs
as the complete parent. The maps need not be inverse on all parent
tuples: (7) is a normalization, and the new system represents the
checksum-one part of the parent zero set.

The fixed universal alphabet and the explicit padded enumeration are
inherited unchanged. Ordinary x is not recoded, and no additional
history, sign, positivity or power predicate is assumed for free.

## 4. Counts and exact degree

The previous source's certificate costs C+4; deleting one multiplication
gives C+3. Its comparisons are unchanged, and exactly one positive
witness disappears. Thus the SOS M/A splits are

    four: M=m+2h+96+f_M-d_M-epsilon-chi,
          A=2m+h+p+127+f_A-d_A-2chi;
    six:  M=m+2h+94+f_M-d_M-epsilon-chi,
          A=2m+h+p+123+f_A-d_A-2chi.

For degree, retain the actual supplied-coordinate convention and the
widened-radix highest part `P*=16(alpha*x+height_slack)*sum Ehat`
when P is computed. The new field F0 has highest part q*, of degree
nu L. This is still strictly below the existing leading q^3 F3 term
in the packed native index. Thus the five surviving unit factors have
exactly the previous highest forms, while the removed checksum factor
had highest part q* of degree nu L.

The new product remains the unique largest residual. Its nonzero
highest part is the product of those five highest forms, and the SOS
has its square as highest part. The exact degree therefore falls by
2nu L from the preceding packet, giving the opening table. The source
audits every individual remaining factor and the full residual degree;
it does not divide a polynomial by q* or impose P=B^t during degree
calculation.

## 5. Literal and positive checks

The [receipt](group_projective_computed_checksum_field.json) stores
twenty compact ledgers and one complete ten-letter source. The checker
compares all parent residuals and the full numeric SOS under the F0
substitution on 1,280 assignments, including 320 signed assignments.
Twenty exact weighted offset polynomial evaluations audit every
remaining unit factor and the residual degree/leading coefficients.
The final SOS is not redundantly expanded symbolically.

Another 512 positive fixtures impose only the outer scalar conditions,
including J=1 and nondyadic P or B, and verify (3)-(5) directly.
For each, two structured native fixtures impose Q=Nk=epsilon_k and
Nl=1, with both physical input ports and the native X bound exact.
All 1,024 positive branch normalizations preserve the entire residual
list and numeric SOS under (7) and field erasure. Their norm residuals
are unrestricted: these are exact algebraic and positivity audits,
not claimed numerical materializations of the enormous Pell witnesses.

Run normally to compare the deterministic receipt, or with `--write`
to regenerate it. All parent packets remain unchanged.

The author regenerated the receipt and ran a fresh default replay;
both passed all recorded checks.

Independent review checked positivity before typing, the negative-branch
normalization, gate accounting and degree forms, replayed the default
receipt, and verified another 256 signed checksum-slice residual/SOS
identities across both variants and both optional compiler switches.
