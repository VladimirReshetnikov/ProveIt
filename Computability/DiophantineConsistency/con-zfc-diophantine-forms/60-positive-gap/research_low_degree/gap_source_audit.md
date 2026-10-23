# Independent audit: positive first-root gaps and a square register shift

Repository pin: `beb0192cb8dc36f78c369c080f2adfbc1887a486`.

This audit concerns the literal 31-positive-variable quadratic source used
by the degree-separated construction. It proves local source equivalence;
it does not certify the inherited native compiler or the final Jones bridge.
All conclusions below hold without assuming consistency or inconsistency.

## 1. Conventions

The arrays contain *weighted records* for coefficient extraction. A constant,
linear monomial, or diagonal quadratic record stores its coefficient in
`2*rho`. A mixed quadratic record stores half its coefficient in `2*rho`,
because the convolution of the encoded word with itself supplies both orders.
Thus record counts are counts of `(row, monomial)` groups, and a coefficient
may itself be an exact polynomial in the four fixed ports.

The relevant zero-based coordinate indices are:

| Index | Original meaning | New meaning |
|---:|---|---|
| 0 | J | unchanged |
| 11 | tau | t = tau - p |
| 12 | eta | unchanged |
| 13 | zeta | unchanged |
| 16 | Q = q^3 | unchanged |
| 17 | E | unchanged |
| 18 | P | p = P - eta - zeta |
| 19 | c | unchanged |
| 20 | a | unchanged |
| 24 | q^2 - 1 | S = q^2 |

Write `k=eta+zeta` and `q=beta*J+1`. The coherent fixed tuple has beta>=1.

## 2. First-root gap substitution

The old source has the equations

    rho4 = a-E-sQ = 0,
    rho6 = c-eta-k(a-E) = 0,
    rho7 = P-k-E(c-eta) = 0,
    rho8 = tau^2-P^2+kP-1 = 0.

The coordinates P and tau occur in no other source rows. Replace

    P = p+k,     tau = p+t.

Exact expansion gives

    rho7' = p-E(c-eta),
    rho8' = t^2+2pt-kp-1.

These are quadratic polynomials. Their weighted record counts are three
and five, compared with five and five before the change. The complete
source therefore changes from 89 to 87 weighted records.

### Forward direction, including strict positivity

At a common positive old-source zero, rho4 gives `a-E=sQ>0`. The equation
rho6 then gives `c-eta=k*sQ>0`, since `k=eta+zeta>=2`. The equation rho7
shows

    p=P-k=E(c-eta)=E*k*sQ>0.

Under this identity, rho8 is

    tau^2=p(p+k)+1 > p^2.

Since tau and p are positive integers, `tau>p`, so `t=tau-p>0`. Every
unchanged coordinate remains positive. The exact expansions prove all new
rows vanish. This argument uses existing source equations, not a claim that
the affine map sends every positive input tuple to a positive tuple.

### Reverse direction

Given a common positive new-source zero, define `P=p+k` and `tau=p+t`.
Both are strictly positive. The two expansion identities give rho7=rho8=0,
and all other rows are unchanged because P and tau are absent from them.
The two transformations are inverse. Thus they define a bijection between
the common positive zero sets, with exactly 31 positive coordinates on
each side.

## 3. Supplying q^2 instead of q^2-1

After the gap substitution, replace coordinate24 by `S=q^2`, meaning that
the old coordinate is `S-1`. The first two old residuals were

    rho1 = old24-beta^2 J^2-2 beta J,
    rho2 = Q-q(old24+1).

They become

    rho1' = S-beta^2 J^2-2 beta J-1,
    rho2' = Q-S-beta J S.

The first row gains one constant record, while the second loses two
records. In the already row-reduced source, only row14 also uses coordinate24.
Its terms `-F-alpha*old24-F*old24` become

    alpha-alpha*S-F*S.

Thus its linear `-F` term is replaced by `+alpha`, with no change in record
count. No other row changes. The final count is **86 weighted records**.

The domain proof is exact. From an old positive zero, S=old24+1>0. Conversely,
the new rho1 forces S=q^2. Since beta>=1 and J>=1, q>=2 and S>=4, so
old24=S-1>=3 is strictly positive. This is again a bijection on common
positive zero sets. It introduces no further parameter and does not alter
any fixed coefficient port.

Every mixed and diagonal quadratic `(row, monomial)` pair, with its complete
coefficient polynomial, is unchanged by this second substitution. Existing
quadratic active-pair isolation certificates therefore remain valid. Linear
and constant kernels, row targets, height and final bounds must still be
regenerated and checked against the new records; the observation alone does
not certify a new final equation.

## 4. Finite exact audit

`audit_gap_source.py` independently converts the weighted records into
ordinary exact polynomials for `2*rho`, performs both substitutions by
integer polynomial multiplication, and checks exact equality against the
87- and 86-record arrays. It also verifies that P and tau are absent from
the other old rows and that the quadratic records are unchanged by the
square-register shift. These are exact finite identities, not numerical
sampling claims. The unbounded strict-positivity proof is Sections 2-3.

The 86-record array is at
`research_nine/data/positive_gap_shift_records.json` and an identical copy
is at `research_low_degree/gap_square_records.json`.

## 5. Other affine gap possibilities inspected

The main Pell root D occurs in a defining row and in `D^2-Delta*c2-1`.
Its positive gap D-X removes one linear record from the defining row, but
adds the mixed term `2*d*X` and `X^2` to the square row: a net increase of
one record. It is not a record-count improvement.

The auxiliary gap y-V is positive at the relevant source zeros. It leaves
the difference-of-squares definition with three records; eliminating the
shared y-square from the auxiliary norm then leaves four records instead
of three. This is again a net increase of one record. No improvement is
claimed from these transformations.

Replacing the f-square register by f^2-1 trades a constant into its defining
row and removes the linear Delta term from the strong equation, for a net
zero record change. It might affect finite packing geometry, but is not an
additional arithmetic or semantic result claimed by this audit.
