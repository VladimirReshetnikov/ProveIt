# An affine obstruction to sharing the two complete84 norm pairs

No operation reduction is claimed. This note gives an all-size algebraic obstruction to a joint affine change of the main and input Pell-coordinate pairs that keeps their product in the same two-norm form. Unlike the earlier finite discriminant-shear census, the coefficients and affine maps here are unrestricted within the stated field. The result does not cover nonlinear norm composition or equivalence only on positive zero sets.

## 1. The actual cut

In the saved complete84 source, use

    a=R12=Y(X+1), H=a4m5=4a+3, Delta=A=(a+1)(a+3),
    c=R10a=kY+eta, k=R10b=eta+zeta,
    kappa=index_rhs=u+delta*Delta,
    mu=exponent_rhs=W+a*kappa+rho*H,
    D=R14=X+a*c+(rho+sigma)*H.

The two actual factors are

    Nmain=D²−Delta*c², Ninput=mu²−Delta*kappa².       (1)

The literal source binds these definitions at rows15–29 and37–47. The already known exact root-sharing rearrangement costs4M+5A for the two roots, just as the parent does. The relation `H=4a+3` makes some formal bilinear-rank arguments inapplicable; the theorem below retains that relation.

For algebraic purposes fix any valid compiler numeral tuple, and take

    K=Q(q,X,Y,k,u,W,F,Z,transport_quotient,f,h,i,
        auxiliary_quotient,tau_root,y_aux).

These15 exterior coordinates exclude `eta,delta,rho,sigma`; together with those four they replace the19 nonfixed supplied coordinates. The change is birational: `J=(q−1)/(B−1)`, `w=X/q`, `s=Y/q³`, `x=(u−inner_bits)/twice_cell_bits`, `zeta=k−eta`, and `alpha=q−F−2Z−(u−inner_bits)−W`. Here `B−1` and `twice_cell_bits` are fixed nonzero numerals. Thus these are legitimate independent rational coordinates on the generic source field, without imposing any norm equation.

Over `K`, the four remaining variables can equally be written as `(D,c,mu,kappa)`. The inverse is

    eta=c−kY,
    delta=(kappa−u)/Delta,
    rho=(mu−W−a*kappa)/H,
    sigma=(D−X−a*c)/H−rho.                           (2)

Both denominators are nonzero elements of this field. Moreover `Delta` is nonsquare in `K`: as a polynomial in the independent `Y` it is the product of the two distinct linear factors `Y(X+1)+1` and `Y(X+1)+3`, each with odd multiplicity. Adjoining the other independent exterior parameters does not change those valuations.

This rational coordinate argument establishes independence for polynomial identities. It is **not** an integer witness substitution, a positive inverse, free arithmetic, or paid input preprocessing.

## 2. Exact affine rigidity

**Theorem.** Let `K` have characteristic zero and let `Delta` be nonsquare in `K`. Write `N(z,t)=z²−Delta*t²`. Suppose an invertible affine `K`-map of the four independent variables `(D,c,mu,kappa)` gives `(D',c',mu',kappa')` and satisfies

    N(D',c') N(mu',kappa') = N(D,c) N(mu,kappa)       (3)

as a polynomial identity. Then its translation is zero. Up to swapping the two coordinate pairs, it consists of separate norm similitudes

    N(D',c')=lambda*N(D,c),
    N(mu',kappa')=lambda^(-1)*N(mu,kappa),            (4)

and neither new pair mixes the two old pairs. Here `lambda` is a nonzero element of `K` and each multiplier is represented by the norm of an element of `K(sqrt(Delta))`.

**Proof.** In `L=K(sqrt(Delta))`, the right-hand side of (3) is the product of the four distinct, independent linear forms

    D+sqrt(Delta)c, D−sqrt(Delta)c,
    mu+sqrt(Delta)kappa, mu−sqrt(Delta)kappa.

Invertibility makes the four corresponding new affine forms nonconstant and independent. Unique factorization in the polynomial ring over `L` forces each to be a nonzero scalar times one of the four old homogeneous linear forms, with each old form used exactly once. Consequently all four new constant terms vanish. This implies that all four translations in the original coordinates vanish as well.

Conjugation over `K` exchanges each new plus form with its new minus form. If a new plus form is a scalar times one old form, its conjugate is the conjugate scalar times precisely that old form's conjugate. Hence one new pair must use both forms of one old pair, rather than taking one form from each pair. The other pair uses the remaining old pair. Multiplying each conjugate pair gives (4); the product of its two scalar multipliers is1 by (3). ∎

Explicitly a separate similitude, possibly followed by conjugation, has the form

    (z,t) -> (p*z+Delta*q*t, q*z+p*t),
    lambda=p²−Delta*q² != 0,

or the same expression after replacing `t` by `−t`. The theorem allows arbitrary such `p,q` in the exterior field; it asserts no cost or positivity property for them.

In particular, within this coefficient field, an affine change that leaves both `c` and `kappa` literally fixed can only change the independent signs of `D` and `mu`. It cannot make one center a genuine affine mixture of the two centers while preserving (3). If the two roots must stay positive on parent positive zeros, their established strict positivity selects the positive signs. This last corollary does **not** allow coefficients depending on `c` or `kappa`: for example such an enlarged coefficient field admits the rational swap `D'=c*mu/kappa`, `mu'=kappa*D/c`. That operation falls outside the four-independent-coordinate theorem and would require its own paid and integral-domain analysis.

## 3. The positive difference does not retain a unit factor

There is also a direct obstruction on the actual parent positive zero set, rather than on all polynomial values. Set

    Bcross=D*mu−Delta*c*kappa.

For every integer `t`, exact expansion gives

    N(D+t*mu,c+t*kappa)
      = Nmain+2t*Bcross+t²*Ninput.                  (5)

At a parent positive zero both old norm factors are1. Therefore (5) is `1+2t*Bcross+t²`, which is even whenever `t` is odd. It cannot replace a factor that must remain1 while all other parent factors are retained. In particular the simple addition or subtraction of the two Pell-coordinate pairs fails immediately.

For subtraction, even positivity does not repair this failure. The accepted parent theorem recovers `D=chi_(a+2)(R)`, `c=psi_(a+2)(R)`, `mu=chi_(a+2)(u)`, `kappa=psi_(a+2)(u)` with `R>u`. Both differences `D−mu` and `c−kappa` are then positive, but their norm in (5) is still even, not1. No numerical example or unexplained sign inference is needed for this obstruction. This is a statement about replacing this factor on the identical old zero; it does not exclude a different finalizer or a coordinated nonlinear change elsewhere.

## 4. Source scope and what remains open

The theorem rules out one precise strategy: obtaining an exact product of the same two norms by an invertible affine mixing of their independent coordinate pairs, with coefficients in the declared exterior field. It classifies affine symmetries, not all ways to compute the unchanged roots more cheaply. It is not an arithmetic lower bound, a classification of all source-coordinate automorphisms, or a rejection of positive charts whose polynomials agree only after a more general substitution. In particular:

- Separate norm similitudes and pair swaps remain possible and must be paid in the actual source.
- Nonlinear norm composition lies outside the theorem; its already tested schedules are separate evidence.
- A chart preserving only the complete positive zero set need not satisfy (3).
- The retained `c²`, `Delta*c²`, input-modulus and auxiliary consumers still have to be reconstructed in any actual source change.

The tempting unrestricted main-root-gap chart is already refuted in `complete80_main_root_gap_collapse.md`; the shared-projection83 relaxation is not proposed again here. There is no new complete source, gate count, witness reduction or universality claim.

All source and prior notes were read inertly. No predecessor, frozen helper, supplied program or builder was executed or imported. Fresh inline metadata code only read JSON/text and computed file hashes; no arithmetic search or test corpus is offered as a substitute for the proof.

Repository directory: `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`.

| Read dependency | SHA256 |
|---|---|
|`complete84_scaled_strong_output.json`|`8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`|
|`complete84_scaled_strong_output.md`|`01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`|
|`complete84_joint_root_cut.md`|`79cfda9e870ad63a848fb454266d1bca98f2117393edc57f99108b4c1cce780c`|
|`complete87_discriminant_shear_scout.md`|`9ef454b65cf75ace91c232d1b0ac643b8c0a00f39c43e16f0ead0666ba414765`|
|`complete80_main_root_gap_collapse.md`, Sections1–5|`7bb2a237dce7c04a373a6c0ad0510decd056785d930c967a9b244598fdcebea9`|
|`complete83_shared_projection_math.md`, interface context only|`1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c`|

The current complete84 theorem remains unchanged. A useful next arithmetic candidate must either exploit a separately paid similitude, use a nonlinear joint evaluation, or prove a positive-zero equivalence outside this affine product-preserving class.
