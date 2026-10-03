# Independent mathematical challenge: target-free three-mass height

The proposed height `h=n0+T+eta` is sufficient for the four current fixed three-mass programs. I found no mathematical obstruction. This is a bounded review of the unmaintained `three_mass_target_free_height_probe`, not a review of a maintained successor API or a new universal arithmetic bound. The source/receipt pins are recorded in the companion independent checker and receipt; no author code is imported or executed.

The reviewed sources are the endpoint projection proof, the complete residue-affine packed-history proof, the unbounded three-mass clock proof, and the prescribed native AND theorem in `native_binary_masked_selection63.md`, with its exact coefficient-factorization successor. This review does not replace their native Pell extension theorem by finite tests.

## Height and native typing

Write `K` for the state-encoding multiplier, `m` for the residue modulus, and `C` for the fixed dyadic radix multiplier. They are distinct constants. In each supplied table, `K=5`, `n0=K*x+1`, and the target is `nf=K*(y-1)+qh`, with natural free inputs `x,y,T`. All supplied auxiliary witnesses, including `eta`, are positive integers. Thus

    h=n0+T+eta >= 2,       0<n0<h,       0<=T<h.

No positivity assumption on `nf` is used here. At `y=0` it is negative in these four tables.

The inherited fixed multiplier satisfies

    C >= max(4,m+1,1+max_s(a_s+d_s),2384*m+2),
    B=C*h^2,       P=(B-1)*J+1.

Consequently `B>=16` already before equations, so the old proof's initial `B>=12` margin is preserved. The shifted selector and product coordinates are nonnegative, and the joined words are nonnegative. The padded native words `16H+12`, `16M+10`, `16A+8` and scale `16Q`, where `Q=B*P^v`, are positive. The native theorem has no independent hypothesis `h>=3`; it accepts every positive prescribed scale and nonnegative unpadded word ports satisfying its relation.

At a complete zero, the unchanged global bound excludes `J=0`: then `P=1`, while the quotient hat plus positive slack alone contribute at least two to its left side. Hence `J>=1` and `P>=B`. The same bound gives `W,Z_a,J<P`, with selector class sums at most `J`. All packed lanes are below `P`, including

    (B-1)*G_a <= (B-1)*J=P-1,
    (h-1)*J < (B-1)*J < P.

Therefore the old joined-lane proof applies. The prescribed native theorem forces `Q` dyadic, hence `B` and `P` dyadic. Because `C` is dyadic, `h^2` and then `h` are dyadic. The divisibility `(B-1)|(P-1)` gives `P=B^t` with integer `t>=1`. The selector/range lanes recover a unique branch in every cell and a quotient `0<=q_i<h`. The current and next state digits satisfy

    1<=c_i=m*q_i+s_i<=m*h<B,
    1<=n_i=a_(s_i)*q_i+d_(s_i)<B.

None of these steps needs the target in the height.

## Target sign and exact clock

Let `Cw=sum c_i*B^i` and `Nw=sum n_i*B^i`. The retained transport equation is

    B*Nw+n0 = Cw+B^t*nf.

Treat `nf` as an arbitrary integer. Modulo `B`, the strict digit bounds force `c_0=n0`. Subtract this equality and divide by `B`. Repeating forces `n_i=c_(i+1)` and finally `nf=n_(t-1)>0`. In particular `y>=1` follows after chronology, rather than serving as an unpaid preliminary hypothesis. A prior bound `nf<h` is unnecessary; the equation itself yields `nf<B`.

The inherited absorbing trap behavior makes such a path a first-halt path. A repeated current encoded state would create a deterministic cycle, so there are at most `m*h` steps. The established physical tick bound is `tau_i<=2384*h`; it remains valid at `h=2`. Therefore

    sum tau_i <= 2384*m*h^2 < B-1,
    (B-1)-2384*m*h^2 >= 2*h^2-1 >= 7,
    0<=T<h<B-1.

The unchanged clock congruence modulo `B-1` is consequently an equality of ordinary times. This proof does not assume a bounded external horizon.

## Fresh-height completeness and the map boundary

For an actual first-halt history and its exact time `T`, choose a dyadic `h` larger than `n0+T` and every occurring quotient. Set `eta=h-n0-T>0`, then rebuild `B,P,J`, the masks, quotient word, selected products, clock quotient and native witnesses at that height. The disjoint selected classes give `sum Z_a<=W<=(h-1)*J`. If `g` is the number of exceptional slope classes, the required positive global slack satisfies

    beta >= (B-2h)*J-g > 0.

Indeed `g<=m-1`, `C>=m+1`, `h>=2`, and `J>=1` give `(C*h^2-2h)*J>=4m`. The clock quotient is nonnegative because `sum tau_i*(B^i-1)>=0`, and its hat is positive. The native extension is supplied at the freshly constructed scale; an old native tuple is not reused.

Thus the target-free construction and the old endpoint construction represent the same ordinary triples for these fixed programs by their common first-halt semantics. This does not establish a positive coordinate map or a bijection with the immediate parent's supplied zero tuples.

The exact algebraic pullback is

    eta_endpoint = eta-K*y-qh,
    eta_coefficient = eta-nf.

It can be negative. Independently, the one-step nop input `x=40`, output `y=41`, time `7880` has `n0=201`, `nf=202`. Choosing `h=8192` gives `eta=111`, `eta_coefficient=-91`, and `eta_endpoint=-96`. This is an outer-history/AND boundary example; complete native Pell witnesses have not been materialized.

## Bounded independent evidence

The checker authenticates nine supplied source/proof/receipt files. It independently identifies the private four-addition height chain in each actual endpoint packet, reconstructs the two-addition chain, checks the affine signed pullback, and verifies literal conservation of every other source row, all nineteen comparisons, coordinates, and the complete finalizer tail. This establishes the source-specific two-addition saving at the proved height cut; it is not a maintained API audit.

Independent finite checks cover 84 actual-radix boundary cases, including `h=2`, and 101,475 complete small digit-word/initial-state combinations. The latter impose no target sign: divisibility determines whether an arbitrary integer target exists, and all 1,259 admitted cases obey exact chronological cancellation and positive final target. The general conclusions above come from the proofs, not from extrapolating this census. No historical suite or giant Pell witness construction was run.

Replay with the endpoint/proof files under `--root` and the three frozen probe files under `--probe-root`:

    python3 review_three_mass_target_free_height_math.py --root WIP --probe-root /tmp --expect review_three_mass_target_free_height_math.json

No claim concerns a universal program table, an ordinary-input universal decoder, global optimality, or a positive same-tuple restoration to the old height interface.
