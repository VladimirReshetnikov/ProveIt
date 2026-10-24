# Exact degree of the eleven-integer parity/interpolation family

All variables are unrestricted integers. The three delivered polynomials use exactly the same arithmetic witnesses and differ only by integral translations of the final coordinate n:

- Direct carrier: exact degree 2912, 200 live binary arithmetic operations.
- Auxiliary-centered carrier: exact degree 2272, 204 operations.
- Auxiliary- and first-Pell-centered carrier: exact degree 2240, 206 operations.

The preferred lower-degree equation is `budget_intersective11_degree2240.json`. Fixed numeral and variable leaves are free in this measure; every live addition, subtraction, multiplication, squaring, and multiplication by a constant costs one gate.

## 1. Literal centers and an exact cancellation cut

Use the notation of PROOF.md. Put L=XY^2k, S=IH^5, and

    Caux=S(2Q−1)V,
    Btau=16S^2(L^2+Lk+1),
    Cnum=4S^2(Q−1)(QV^2−1),
    d=B^2 Dm,
    Astrong=S^2 Df,
    e=64S^2 Dg,
    s0=Sn−A.

Here A,B without subscripts are the two coefficients of the homogeneous intersective quintic in the main square root. They must not be confused with Astrong or Btau.

The direct, auxiliary-centered, and twice-centered norm centers are respectively

    s0,
    Caux+s0,
    Caux+4SL+s0.

Both shears are integer polynomials independent of n. The exact identities

    Cnum−Caux^2 = S^2(−V^2−4Q+4),
    Btau−(4SL)^2 = 16S^2(Lk+1)

explain the canceled high-degree terms.

For an exact sparse check take independent indeterminates

    (S,Q,V,L,k,s0,d,Astrong,e)

of weights

    (34,32,25,17,7,35,70,88,94).

Compute the three-root norm with inner radicands Astrong,Btau,Cnum in the free biquadratic algebra whose outer radicands are d,e. Its four basis-weight offsets are (0,35,47,82). The independently expanded successive component degrees are:

    Direct:
      (182,70,82,82),
      (364,252,264,264),
      (728,616,628,628).

    Auxiliary-centered:
      (126,126,138,82),
      (284,252,264,264),
      (568,536,548,548).

    Twice-centered:
      (142,126,138,82),
      (276,268,280,264),
      (560,544,556,548).

In each case the scalar coefficient strictly dominates at the final three-root stage. The remaining two quadratic norms therefore raise its leading part to the fourth power. Its scalar leading parts are, respectively,

    256 S^8 Q^8 V^8,
    65536 S^8 Q^4 V^4 L^4,
    16384 S^6 Q^4 V^4 L^2 e.

Consequently the upper bounds are 4×728=2912, 4×568=2272, and 4×560=2240. `check_degree.py` verifies these equalities by exact sparse integer arithmetic, not by random degree sampling.

## 2. Nonzero leading coefficients after authentic specialization

Let

    q0=6 beta j, W0=12w, Y0=2v q0^3,
    a0=q0 W0 Y0, I0=2src^2,
    Q0=a0^4 I0^2, S0=I0(4a0)^5,
    R0=q0^4z−12q0^3wC,
    V0=a0^2 I0^2(4I0T−R0),
    L0=h a0^2Y0,
    Dg0=−48q0^2Y0^2h^2a0^2s^2,
    e0=64S0^2Dg0.

These are the actual leading forms of the delivered front end. In particular the degree-24 budget top part is −4q0^2(Y0h a0)^2. Its coefficient is unaffected by any relation among the other five fixed numerals.

For the twice-centered polynomial the full degree-2240 homogeneous part is

    2^56 S0^24 Q0^16 V0^16 L0^8 e0^4.

Selecting the maximal T exponent chooses 4I0T in every factor of V0's bracket. Every remaining factor is a monomial. This gives the exact coefficient

    [j^1176 w^280 v^296 h^16 s^120 r^112 c^224 T^16] P2240
       = 2^2592 3^1460 beta^1176 > 0.

The exponents sum to 2240. Hence the upper bound is attained for the actual fixed coefficient tuple. Neither an abstract generic-coefficient assumption nor a probable noncancellation argument is needed.

The same maximal-T selection applied to the other two scalar leading forms gives nonzero monomials of degrees 2272 and 2912. Their complete integer coefficients and exponent dictionaries are recorded and verified in DEGREE_CHECK.json and both CHECK receipts. Each coefficient is independent of K0,MC,MF,cone_A,cone_B.

## 3. Independent interpretation of the cancellation

In a formal Laurent expansion in a common degree parameter, the auxiliary root's polynomial center has degree91 and its error has degree27; the first-Pell center has degree51 and its error has degree41. For the twice-centered norm, sixteen sign factors have degree91, eight have degree51, and the remaining eight are dominated by the guard root of degree47. Thus

    16×91+8×51+8×47=2240.

This is an independent explanation of the exact sparse cut, not a substitute for the nonzero specialized coefficient above.

## 4. Reproduction and scope

Run `python build.py`, `python check.py`, and `python -O check.py` from this directory. The scripts use the sibling `guard` directory's exact coefficient payloads, formal-polynomial tools, and 83-gate norm evaluator. They require only the Python standard library and no network. The complete delivered bundle contains those dependencies.

Each literal circuit is independently checked at every named front-register dependency cut and against all 20,349 coefficients of a reverse-order formal conjugate product. The arithmetic checks authenticate the equation and its metrics. The unbounded squareclass, interpolation, signed-rank, centered-binomial, and inherited native calibration arguments are stated separately in PROOF.md.
