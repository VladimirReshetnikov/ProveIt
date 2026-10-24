# Independent review: a common Pell infrastructure for all positive powers

## Verdict

The proposed sharing is sound and complete for any finite nonempty family
of positive-base, positive-exponent power calls. A single common majorant
Pell solution `(W,A,Z)`, a single common divisibility Pell solution `(U,V)`,
and a single common CRT parameter `B` suffice. Individual `(X_j,Y_j)` and
`(S_j,R_j)` pairs, bounds and congruence quotients remain per call.

The proof below uses the Pell-sequence facts already appearing in the
reviewed Mathlib `matiyasevic` and `eq_pow_of_pell` proofs. There is no
appeal to a finite search for witnesses, and their enormous possible sizes
do not affect the dimension count.

## 1. Family and common majorant

Index calls by a finite nonempty set `j=1,...,r`. Their mathematical
inputs satisfy `n_j,k_j >= 1`, and the desired outputs are
`m_j=n_j^k_j`. Set

    W = sum_j (n_j+k_j),
    A = X_{W+1}(W),
    W Z = Y_{W+1}(W).

Then `n_j <= W` and `k_j <= W` for every `j`, and `W>=2`.
The congruence `Y_{W+1}(W)=W (mod W)` supplies natural `Z`.
The common last Pell norm is satisfied, and `A>=2`.
For each call,

    n_j^k_j <= n_j^W < (W+1)^W <= A.

The standard power-certificate lemma consequently gives

    0 < m_j < T_j := 2 A n_j - n_j^2 - 1.

Define main pairs `X_j=X_A(k_j)`, `Y_j=Y_A(k_j)`. They satisfy the main
norm and `Y_j>=k_j>=1`. All this uses one and the same `A`.

## 2. A common multiple for all divisibility requirements

Take

    M = 2 product_j (k_j Y_j),
    U = X_A(M),   V = Y_A(M).

Every factor `k_jY_j` is a positive integer, so `M>=2` and
`k_jY_j | M`. The standard Pell divisibility facts used in Mathlib are

    Y_A(k_j)^2 | Y_A(k_j Y_A(k_j)),
    d | M  ==>  Y_A(d) | Y_A(M).

Composing them proves `Y_j^2 | V` for every `j`. Thus all natural
witnesses `vd_j=V/Y_j^2-1` exist, since the positive divisible integer
`V` is at least `Y_j^2`.

The factor 2 in `M` makes it even. The recurrence gives
`Y_A(t)=t (mod 2)` for every integral `A`; hence `V` is even.
The Pell norm gives `gcd(U,V)=1`, so `U` is odd and is coprime to each
`Y_j`. Therefore

    gcd(U, 4 product_j Y_j) = 1.

Strict increase of the positive Pell x-sequence and `M>=2` also give
`U>A`.

## 3. One common CRT parameter

Put `L=4 product_j Y_j`. By the coprimality just proved, choose a
nonnegative integer `B` with

    B=A (mod U),   B=1 (mod L).

Since `0<=A<U`, the first congruence forces `B>=A>=2`, and hence

    B=A+U q_B,    q_B in N.

Because `4Y_j | L`, for each call `B=1 (mod 4Y_j)`. Its quotient is
positive: `(B-1)/(4Y_j)>=1`, as a zero quotient would give `B=1`.
Consequently all per-call rows

    B = 1 + 4Y_j(q4_j+1),   q4_j in N

hold simultaneously. There is no requirement that the different
quotients `q4_j` be equal.

Define `S_j=X_B(k_j)` and `R_j=Y_B(k_j)`. Polynomial dependence of the
Pell sequences on their base gives `S_j=X_j (mod U)` because `B=A
(mod U)`. Also `Y_B(k_j)=k_j (mod B-1)`, so `R_j=k_j (mod 4Y_j)`.
Base monotonicity gives `S_j>=X_j`; the elementary ordinate bound gives
`R_j>=k_j`. Thus every oriented natural quotient exists:

    S_j=X_j+U qS_j,
    R_j=k_j+4Y_j qR_j.

The third norm for each pair holds by construction.

## 4. Per-call power congruence

The common `A` changes no part of the power-congruence argument. For each
call,

    L_j := X_j+n_jY_j-AY_j
         = n_jY_A(k_j)-Y_A(k_j-1) > 0.

The standard Pell power lemma gives `L_j=m_j (mod T_j)`.
Since `0<m_j<T_j`, its quotient is nonnegative, so

    X_j+n_jY_j=AY_j+m_j+T_j qP_j,   qP_j in N.

The natural output-gap witness is `T_j-m_j-1`, and the index-gap witness
is `Y_j-k_j`.

## 5. Soundness of the shared system

Start from any natural solution of the shared polynomial system, with
positive call inputs. Its one affine majorant equation gives
`W>=n_j,k_j` separately for every call. A retained `T_j` definition and
positive output gap already imply `A>=2` without using a Pell theorem:
if `A<=1`, then `2An_j<=2n_j<=n_j^2+1`, contradicting
`2An_j=T_j+n_j^2+1` with `T_j>=1`.

For a fixed `j`, use the shared `W,A,Z,U,V,B,q_B` as that call's old
private witnesses. Its own rows give all original hypotheses:
the three norms, `Y_j>=k_j`, `V>0`, `Y_j^2|V`, `B>=2`, and all four
required congruences. Here `Y_j>=k_j>=1` makes the positive-multiple row
imply `V>0`, and its `q4_j+1` row makes `B>=5`.
The old power theorem therefore yields `m_j=n_j^k_j`.

This argument does not need to prove that an arbitrary shared `(U,V)`
arises from the particular completeness index `M`. The explicit `M` is
used solely to prove simultaneous existence.

## 6. Order of construction and absence of circularity

The high-level macro graph may use earlier power outputs as later bases
or exponents. For completeness, first assign the intended mathematical
values to all high-level outputs and their ordinary arithmetic inputs.
Then the finite list of `n_j,k_j` is fixed. Choose `W,A,Z`, then all
main Pell pairs, then `M,U,V`, then `B`, then the remaining per-call
pairs and quotients, exactly in the order above.

This works provided no high-level input is defined using a private Pell
certificate witness such as `A,U,V,B`. The reviewed builder's high-level
interfaces expose only the mathematical power output, so that condition
holds. The self-bounding factorial construction also satisfies it:
choose its intended output `n!` first; its radius depends on that output,
not on the common Pell witnesses.

For soundness, prove each power graph pointwise from the shared system.
Then invoke the independent factorial, binomial and source-calculus
lemmas. No assumption of correct factorial outputs is needed to justify
the power graph.

## 7. Scope

This is a uniform finite-family ordinary proof formalizable in ZFC.
The auxiliary product defining `M` and CRT construction of `B` occur only
in the existence proof; neither is an extra operation or variable of the
displayed compiled equation. The emitted equation contains the shared
quadratic rows and per-call rows. The number of calls and every equation
row must still be measured from the literal generated artifact.
