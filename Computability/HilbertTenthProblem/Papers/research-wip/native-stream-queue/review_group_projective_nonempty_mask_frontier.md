# Independent review of the nonempty projective mask frontier

**PASS; no author correction requested.** The two complete saved Nielsen sources cost370=149M+221A at exact degree4909 and371=150M+221A at exact degree3517. Both retain54 positive witnesses, six comparisons and the17-operation finalizer. They preserve the full positive-zero projection onto the ordinary input and outer history/controller coordinates. Fresh native witnesses establish this equivalence; the polynomials and native fibres are not identified.

The [independent checker](review_group_projective_nonempty_mask_frontier.py) authenticates the complete frozen [author trio](group_projective_nonempty_mask_frontier.md) and all41 declared dependency files. It reads the actual Nielsen parent from `group_projective_inverse_macro_sharing.json`, imports no author or historical Python, and reconstructs both complete source arrays independently. All pins and full source hashes appear in the [independent receipt](review_group_projective_nonempty_mask_frontier.json). Generic ring/coefficient helpers are reused from this reviewer's previous top-mask review; the scalar constructions, degree expansions and accepting fixtures here are new checks on the two actual sources.

## Source and complete ledger

Both source arrays delete the parent's private `range_Bminus_shift=2*range_body_scale` multiplication and alias its sole consumer to the already paid `range_body_scale`. The reused32 variant makes no other arithmetic change.

The separate8 variant additionally inserts exactly one multiplication `range_origin8=J*R8(P)`, routes the range-mask product through it, and changes the existing `range_body_scale` multiplication from `T*P32` to `T*P8`. The original controller `J*R32(P)` remains. P32 remains live in `T=P40`; the P8 and R8 expressions were already paid. The reviewer checks every parent multiplication and finds no already-paid J*R8 product.

The expected instruction arrays must match the saved children exactly. The inherited graph, edge hats, lane placement, free coordinates, domains, all six comparisons, and all17 actual finalizer rows are preserved. Every gate and declared free input must be live.

| Variant | Certificate | Full polynomial | Witnesses | Comparisons | Exact degree |
|---|---:|---:|---:|---:|---:|
| reused32 |353=143M+210A|370=149M+221A|54|6|4909|
| separate8 |354=144M+210A|371=150M+221A|54|6|3517|

The comparison named `eight_units=1` is the product of seven actual factors. The output is exactly that product times one plus the sum of five squared outer residuals, minus1. Independent expansion at the actual factor and comparison ports proves the full finalizer in both cases. This pays6M+11A beyond the certificate in each source; no omitted AND, matrix, power or sequence primitive is charged as free.

## Independent scalar reconstruction

For each source the checker reconstructs all twelve graph/scale cuts directly from the28 literal edges and their32-lane injection. For `E_e=Ehat_e−1`, these are J, the physical packed selector S, controller packed word C, weighted flow left/right, four physical update sums, controller origin, T and T2. No private-path identity is assumed to imply a different graph's flow.

It then expands31 additional joined scalar polynomials across the two packets. These include the actual P8/P32 and R8/R32 producers, controller origin, range cell and mask, lower H/M blocks, complete H/M/Z and q. For k=32 or8 the verified formulas are

```
O = J*R32(P),        T=P40,        T2=P^(40+k),
R = (2D−1)*J*Rk(P),
H = h+P8*C+T*h+B*T2,
M = m+P8*O+T*R+T2,
Z = z+P8*C+T*h,
q = 32*B*T2.
```

Here h,m,z are the unchanged physical eight-lane words. The extra scalar proof for separate8 checks its new J*R8 gate itself. A common abstract interface at the three changed ports then proves740 complete retained-register identities and the final outputs. This means equality after replacing the actual changed scalar interface, not equality at the same original supplied tuple. The five outer residuals are identical as full polynomials without those cuts.

For reused32 the previously reviewed top-mask correction still applies: the index factor changes by `16*T2*(q²−1)`, the other six factors are unchanged, and the whole correction is that quantity times their product and the positive outer square-sum factor. Separate8 changes q and further native quantities; no such same-coordinate correction is claimed for it.

## Positive proof before and after typing

At any full positive integer zero, the finalizer first forces all five outer residuals to vanish and every integer factor to be a unit. For either possible sign of the joint unit, the retained joint-bound argument gives P≥12, histories below P, selected-source words below P, and then J≥1 and B≤P from `P=(B−1)J+1`. The literal ordinary-input prefix gives `u=24x+13≥37`, `D=u+height_slack≥38`, and `B=16D≥608>32`. No Boolean, power or endpoint interpretation is needed to obtain that margin.

The physical words are below P8 and the controller words are below P32. Also `(2D−1)J<P`, since B=16D and `(B−1)J=P−1`. Hence the range word has width k in base P, without coefficient carry. The complete lower physical/controller blocks lie below P40. Appending the shifted physical/range blocks therefore gives

```
0 ≤ H0,M0,Z < P^(40+k)=T2.
```

In particular P48 is sufficient only because the range mask has also been shortened to8 lanes. The controller remains32 lanes. Using the unit top mask, the ordinary integer inequalities are

```
H−Z ≥ (B−1)T2+1,
M−Z ≥ 1,
2B*T2−H−M+Z ≥ (B−3)T2+2.
```

They imply positivity of the four reconstructed fields, residues1,4,2,8 modulo16 and checksum q−1 before native typing. The unchanged tail coordinate gives `X=q(w+(q−1)F3)`, `Y≥3q`, and therefore `XY>2r+3` without first assuming X>r. All hypotheses of the pinned native sign/rank/index argument apply to either scale. It restores native units and the joint unit to+1, then q dyadic. From `q=32BP^(40+k)` it follows that B and P are dyadic; the repunit gives `P=B^t`.

Only now is binary separation used. The top block vanishes because `B AND1=0`. The physical and controller regions are identical. In the range region, h<P8 and

```
((2D−1)*J*R32(P)) mod P8 = (2D−1)*J*R8(P).
```

The exact low-eight-bit-block equality holds because P is dyadic and all base-P coefficients are below P. It follows that `h AND range_mask=h` has exactly the same truth value for both range masks. The extra24 high lanes contain no history bits. This does not assert a polynomial identity between the masks.

Take the outer coordinates of any old or new positive zero. The decoded radix, true history, controller and lower AND conditions now satisfy either range recipe and either old/new top coefficient. The scalar bounds give positive native fields at the corresponding actual q and packed index. The prescribed native converse, including the retained first-root/coupled/tail coordinate constructions, supplies fresh positive native witnesses without changing those outer coordinates. This proves equality of the full outer projections, not merely equality on the tested x values. It is not a signed/rational-zero theorem or a bijection of native fibres.

## Exact degree and the nonempty predicate

All supplied coordinates, including x, have degree1; fixed numerals have degree0. The reviewer guards the main-norm source cone and independently expands its all-value cancellation before propagating an upper bound. It then expands each entire source as a univariate polynomial modulo1000000007 after assigning every free coordinate t. A nonzero coefficient at the upper bound proves exact attainment for the actual fixed-numeral source.

The seven factor degrees are respectively

```
reused32:  679,1210,884,532,532,1064,2;
separate8: 487,874,596,388,388,776,2.
```

The outer square sum contributes degree6, giving4909 and3517. This agrees with the inherited formula `73+2*(29*a_scale+7*m+106)` at m32 and a_scale72/48. In particular F3 retains degree95 in both layouts, while q has degree145 or97; the smaller scale still satisfies Q>F. The naive graph bounds5055/3615 are not treated as exact. No equation holding only at zeros is used to lower degree.

The source inherits the Nielsen table `(R,U^5,inverse(R),inverse(U^5))`, with `R=(2,3,6,7)` and `U=(1,5)`. For positive x≡2 mod5, u=24x+13 satisfies u≡1 mod5 and the accepted physical word `R U^(u−1)` sends `(1,u,1,u)` to `(0,1,0,1)`. The pinned predecessor's modulo5 orbit excludes x=1. Thus this is a proper nonempty input predicate, not an empty-table arithmetic benchmark. No exact residue-class classification or numerical universal alphabet is claimed.

The independent checker constructs x2 and x7 computations in each source, using D256 and D512 respectively—twice the author's fixture heights. It finds actual graph paths and directly executes all124/364 physical letters. The resulting positive chronological words satisfy all five complete outer residuals, joint unit1, both full scalar ANDs and every reconstructed native field's positivity. These are genuine accepted outer histories. Their full positive Pell extensions come from the theorem; enormous native tuples are not materialized.

## Evidence and reproduction

The independent receipt records two complete arrays with741 live gates;24 graph/scale and31 joined-scalar polynomial identities;740 changed-interface register identities; ten unchanged outer residuals;34 retained finalizer gates; two full-finalizer expansions; and two whole-polynomial dense degree expansions. Twelve complete changed-interface/finalizer evaluations include four rational assignments. Thirty-six pretyping cases cover both joint signs and nondyadic scales;60 additional exact cases check the typed range-mask equivalence. Four independently generated accepting outer histories use the two positive inputs above.

```
python3 review_group_projective_nonempty_mask_frontier.py \
  --root /absolute/path/to/native-stream-queue \
  --expect /absolute/path/to/review_group_projective_nonempty_mask_frontier.json
```

`--author-root` optionally supplies a separate directory containing the frozen author trio; otherwise it is `--root`. Pin mismatches fail before checking sources. Optimized Python is explicitly rejected because this reviewer uses assertions. The writer and fresh exact receipt replay run from `/` pass. No historical60-schedule census, public compiler API audit, new optimization census, repository edit or universal numerical-bound claim is included.
