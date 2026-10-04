# Exact auxiliary minimum for the fixed outer counterfamily

## Source boundary and main claim

Source: `BASE_COUNTERFAMILY.md`, recovered proof SHA256
`690c5a1dc237bd53a9582bfbe01fcd8a176174e6b116089a1842532f83c1770b`, read as data. This note executes no upstream Python or saved schedule and does not materialize a complete witness tuple. All finite checks below are independently authored and corroborative only.

**Main theorem (fixed i=1 and fixed strong witness).** Fix any outer tuple constructed in the cited counterfamily. Keep `i=1` and `F_aux=Delta*c^4+1`. Among all auxiliary integer solutions completing the output to zero with `U_aux>0` and `y_aux>0`, the construction's index `R` is the exact least Pell index. Its displayed `y_aux=psi_S(R)` and `U_aux` are simultaneously the unique coordinatewise minimum, where `S=Delta*c^2`. This is a minimality claim for this fixed outer tuple, not for all witnesses of the chart.

## 1. The relevant outer inequalities and congruences

The source gives `R=3 (mod 4)`, `p=0 (mod 4)`, and `A=2 (mod 4)`. The recurrence

    psi_A(0)=0, psi_A(1)=1,
    psi_A(j+2)=2A*psi_A(j+1)-psi_A(j)

has values `0,1,4,7,0,1,...` modulo 8 when `A=2 (mod 4)`. Thus `c=psi_A(p)` is divisible by 8.

In Branch A, `R=6u-epsilon<8u=2p`; in Branch B, `R=28v-1<40v=2p`. Since `p>=12` and `A>=2`, the source's lower bound gives

    c >= (2A-1)^(p-1) >= 3^(p-1) > 4p > 2R.

In particular, `0<R<c/2`.

## 2. Complete fundamental-unit classification

The fixed outer product is `P5=1`, while the specified strong witness gives `Qs=1`. Thus a zero of the complete output requires

    (S*V)^2-(S^2-1)*y_aux^2=1,
    V=c*(U_aux-1)-R*F_aux.

Put `d=S^2-1`. It is positive and nonsquare, since `(S-1)^2<d<S^2` for `S>=2`. Every positive integer solution `x^2-d*y^2=1`, `y>0`, is a power of `S+sqrt(d)`. Here is a direct proof, including the absence of a smaller fundamental unit in the integer-coordinate Pell problem.

For `y=1`, necessarily `x=S`. For `y>1`, multiply `x+y*sqrt(d)` by `S-sqrt(d)` and write

    x'=S*x-d*y,   y'=S*y-x.

We have `x<S*y`, because `x^2=S^2*y^2-y^2+1<S^2*y^2`, so `y'>0`. Also `x>sqrt(d)*y>(S-1)*y`, giving `y'<y`. Finally `x'>0`, since `x>sqrt(d)*y` and `S*sqrt(d)>d`. The new pair is integral and has norm one. Repeated descent reaches `(S,1)`, then `(1,0)`. Reversing it proves the claim.

Applying this to `x=abs(S*V)` shows that **every** auxiliary solution with `y_aux>0` has

    S*V=+chi_S(m) or -chi_S(m),
    y_aux=psi_S(m),                 m>=1.

This classification is for integer pairs `x,y`; it does not assert anything about a larger quadratic-integer ring.

## 3. Even indices and negative V are impossible

The chi recurrence modulo `S` gives

    chi_S(2j)=(-1)^j (mod S),
    chi_S(2j+1)=0 (mod S).

Since `S>1`, divisibility by `S` forces `m` odd. Write `m=2j+1`. The source's exact odd polynomial identity gives

    v_m := chi_S(m)/S = (-1)^j*m (mod c).

Every positive `v_m` is `1 (mod 4)`: when `m=1 (mod 4)` the displayed constant is `m`, and when `m=3 (mod 4)` it is `-m`. But `F_aux=1 (mod c)`, so the literal source argument requires

    V=-R (mod c), hence V=1 (mod 4).

As `4|c`, the negative choice `V=-v_m` is `3 (mod 4)` and is impossible. No sign case is omitted.

## 4. Exact index classes and minimum

For positive `V`, admissibility is equivalent to

    m=R (mod c),  m=3 (mod 4),
    or
    m=-R (mod c), m=1 (mod 4).

Because `4|c` and `R=3 (mod 4)`, these are simply

    m=+R or -R (mod c).

The exact least positive admissible index is therefore `min(r,c-r)`, where `r=R mod c` and `0<r<c`. Here `0<R<c/2`, so it is **R**, and the next admissible positive index is `c-R`.

Both `chi_S(m)` and `psi_S(m)` are strictly increasing for `m>=1`. Consequently `m=R` minimizes `V`, `y_aux`, and

    U_aux=(V+R*F_aux)/c+1.

They are positive at this minimum. In particular, every such solution obeys

    log_2(y_aux) >= (R-1)*log_2(2S-1).

Thus replacing the auxiliary power by another Pell solution cannot reduce this fixed outer tuple's auxiliary height. This does not rule out a different outer construction.

## Second theorem: allowing every positive i with the same outer tuple

This extension is not needed for the fixed-i theorem above. Like the whole new packet, it remains subject to the separate mathematical audit.

Fix the same outer tuple but now allow any positive integer `i` and any integer `F_aux`, with all auxiliary coordinates required positive. Write `S=i*Delta*c^2`. A zero output requires `Na*Qs=1`, so the only integer possibilities are both `+1` or both `-1`. Since `4|S`,

    Na=S^2*V^2-(S^2-1)*y_aux^2 = y_aux^2 (mod 4).

The value `Na=-1` is impossible. Thus necessarily

    Na=Qs=1,
    F_aux=Delta*i^2*c^4+1.

The proof in Sections 2-4 applies unchanged: `c|S`, `F_aux=1 (mod c)`, and the same outer `8|c` and `R<c/2` hold. Every solution therefore has positive `V` and index `m=+R or -R (mod c)`, hence `m>=R`.

For integer `m>=2`, the binomial expansion

    psi_S(m) = sum over odd k in [1,m] of
               binom(m,k)*S^(m-k)*(S^2-1)^((k-1)/2)

has nonnegative terms increasing in real `S>=2`; the `k=1` term is strictly increasing. Thus `psi_S(m)` is strictly increasing in `S`. Since `S=i*Delta*c^2`, the unique minimum of `y_aux` over all such extensions is again attained at `i=1,m=R`.

For odd `m>=3`, the analogous even-k expansion of `chi_S(m)/S` also has nonnegative terms and is strictly increasing in `S`. Combined with monotonicity in `m` and the strict increase of `F_aux` with `i`, this also minimizes `U_aux`. The minimum of `F_aux` is attained whenever `i=1`, regardless of the admissible index; the unique joint minimum of all these coordinates occurs at `i=1,m=R`.

## Independent finite checks

`auxiliary_minimum_check.py` checks the actual `8|c` sign and index classes, recurrence parity, positive Pell descent and classification, the outer recurrence residue and coarse size inequality, the modulo-4 exclusion of `Na=-1`, and bounded variable-i monotonicity. Its machine-readable results are in `AUX_CHECKS.json and AUX_CHECKS_O.json`. These checks use small standalone parameters; they are not genuine compiled instances and do not prove the unbounded statements above.

Both normal and optimized runs use explicit checks, so optimization does not disable the tests. Their receipts are byte-identical. The source binding is independently checked by height_check.py; no source program or saved graph is executed.
