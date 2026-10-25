# Reuse two existing weighted pairs in the Round16 strict product

This is a code-free addendum to the accepted ordinary square-radix/remainder proposal `research/round16-square-radix-compression/`, manifest `aeb8e0988d86b7dd08e15e7db439ba1122a7095a93b311e26e07d2caaf5dabad`. It supplies a different presentation of its strict product using two existing affine expressions. It also records a separate private-slot option for Hstar. No source, materializer, checker, compiler or endpoint is supplied or executed. No accepted source, projection, page or Lean file is changed.

The only arithmetic/program activity in preparing this note was inert text/JSON/ZIP/hash inspection and finite data/occurrence comparisons. No incoming or repository application module was imported, compiled or run. Five rather than seven new partial-product definitions is a symbolic presentation fact below. It is not an accepted raw or projected variable saving.

## 1. Exact source and prerequisites

All coordinates and rows refer to source131's `direct/cap_cofinal_self/source.json` (SHA256 `110c68baefdd955bd5af9af44564e81b9a43a08a088a3424c913bc185178a845`) and `guarded.json` (SHA256 `6cc3a1548b5829159f7c171d4c3e904d4448557becfb540efb809e23887cc817`). They are the original Round16 archive members, not the accepted327 source. The whole old input has 541 coordinates/398 body rows; its guarded form has 622 coordinates/425 rows. These are input descriptions, not proposed endpoint measurements.

Write `F=v3` and `a_j=v_j+1` for j=16..24. The strict-eight factors are a16,...,a23; a24 is restored independently. This addendum assumes exactly the corrected Hstar architecture, all eleven explicit raw-remainder substitutions `r=1+q*u`, their fresh `u*s` graphs, and the optional x-fused chronology in the parent proposal. It does not apply that chronology to the unchanged incoming raw-remainder body.

In particular the retained positive-A cap/frame, square horizon, q request and same-pair base-F²+1 request restore F>=1 before x or the eight CRT scalar signs are used. The K and signed-Qx arguments then restore the required output residues using divisibility before positivity. All nine a_j are nonnegative before any strict product is invoked. The reciprocal-index rows restore a24>=1 independently. No new partial product or affine expression is added to the frame or any power request.

## 2. Actual existing weighted-pair identities

Four exact body rows suffice:

| Row | Exact residual |
| ---: | --- |
| 123 | `v139 - F*(v17+1)` |
| 124 | `v140 - (v21+1)*(1+v139)` |
| 125 | `v141 - F*(v16+1)` |
| 127 | `v143 - (v20+1)*(1+v141)` |

These are the actual full residuals after collecting their affine factors; no row is replaced. Define the affine expressions

    E_A = v143-v20-1,
    E_B = v140-v21-1.

At every integer zero of the retained body,

    E_A = F*a16*a20,
    E_B = F*a17*a21.                              (1)

The complete polynomial consequences are

    E_A-F*a16*a20 = row127 + a20*row125,
    E_B-F*a17*a21 = row124 + a21*row123.

Thus no division by F or a proposed nonzero factor is used. Although the right sides of (1) have total degree three when expanded in their semantic factors, E_A and E_B are affine in existing source coordinates. A row multiplying E_A and E_B, or either by a new partial product, is quadratic.

The complete old guarded-source occurrences are:

| Coordinate | Name | All occurrence rows |
| ---: | --- | --- |
| 139 | `mul.337` | 123,124,132 |
| 140 | `mul.339` | 124,129 |
| 141 | `mul.340` | 125,127 |
| 143 | `mul.344` | 127,128 |

These old gates are retained body ports, not private guard witnesses available to delete. The weighted presentation adds new consumers of them. All original rows and occurrences remain. The new variable namespace must be disjoint from every old coordinate and all eleven refreshed interval triples.

## 3. Five definitions and one directly quadratic fused graph

Adjoin five unrestricted monic partial-product coordinates p2,...,p6:

    p2 = E_A*E_B,
    p3 = p2*a18,
    p4 = p3*a19,
    p5 = p4*a22,
    p6 = p5*a23.                                  (2)

Every row in (2) is quadratic, including the expanded product of the two affine expressions in its first row. They have a unique integer extension at fixed old coordinates. There is no sign graph on an intermediate product. By (1),

    p6 = F^2 * P8,
    P8 = a16*a17*a18*a19*a20*a21*a22*a23.          (3)

Instead of the parent's seven-definition P8 chain and its x-fused graph, use (2) and one fresh Legendre graph

    (x+1)*p6-1 = z1^2+z2^2+z3*(z3+1).            (4)

All three z coordinates are fresh unrestricted integers. Equation (4) is directly quadratic, with no additional x-product gate. The input x is v1. The represented integer differs from the parent's `(x+1)*P8-1`; its old triple must never be reused for the new integer.

The guards removed are exactly the parent x-fused policy's x graph398 with private541..543 and CRT scalar graphs401..409 with private550..576. Whole guarded-source occurrence inspection confirms each of these 30 old private coordinates occurs only in its own removed graph. Every retained original body row, remaining guard, power/frame/cap port and unaffected private witness is fixed by this product presentation change.

## 4. Sign chronology and both existential maps

Start with a zero of the weighted repaired source. Before using (4), apply only the parent's sign-independent Hstar/positive-A cap/request chronology. This proves F>=1 and the nine successor residues; negative target orientation would give -1 rather than 1 modulo q. Hence all a16,...,a24 are nonnegative. The old reciprocal-index contradiction restores a24>=1 independently of the product.

At this stage both E_A and E_B in (1) are nonnegative, and all four remaining factors in (2) are nonnegative. Thus p6>=0 before (4) is used. Equation (4) implies `(x+1)*p6>=1`, so p6>0 and x+1>0. By F>=1 and (3), P8>0. Each of its eight nonnegative integer factors is therefore strictly positive. This restores x>=0 and all eight required scalar signs. Only now use positive Qx and the weighted interval lemma to restore the eleven remainder/slack signs and reconstruct the original scalar/interval triples, as in the parent proof. There is no early positivity assumption on Qx or its denominators.

This proves weighted-source soundness via the parent's complete ordinary architecture and retained source131/C222 calibration. In particular it is not an unchanged-body claim about an old324 polynomial.

There is also a precise pointwise kernel equivalence with the parent's x-fused repaired source. From a weighted zero, keep every common old body coordinate and unaffected witness. The preceding argument gives `(x+1)*P8>=1`. Fill the parent's seven partial products uniquely and choose a fresh triple for `(x+1)*P8-1`; discard the five weighted partial products and their triple. Conversely, from a parent x-fused zero its ordinary proof restores F>=1, x+1>=1 and P8>=1. Fill (2) uniquely, so `(x+1)*F²*P8>=1`, and choose a fresh triple for (4), discarding the old seven-product chain/triple. Existence of each fresh triple is the same standard integer Legendre representation used by the parent.

These two maps preserve the whole common repaired kernel, including F,v140,v143 and all eleven reparameterized remainders. They need not preserve private representations and are not inverse bijections on triples. Composing with the parent's explicit remainder maps gives the old raw-remainder architecture equivalence. Composing with a finite refutation's canonical construction gives fresh positive witnesses for every required semantic input, while all added chain/Legendre coordinates remain unrestricted integers.

For the x-retained version, replacing the strict P8 predicate by `p6-1>=0` has the same proof. The x-fused form (4) is the primary policy of this note; no two predicates are conflated.

## 5. Bounded reuse search and the old324 retention evidence

A bounded inspection of the actual monic constructor products found three direct affine weighted-pair identities over the eight factors:

    v143-a20 = F*a16*a20,
    v140-a21 = F*a17*a21,
    v148-a20 = F*a17*a20.                         (5)

The third follows from actual rows123/132. Among these explicit edges, the maximum disjoint matching has size two, attained by the first two. Products involving v162 or v164 instead carry a22 or a23 multiplied by positive factors involving y and a24+1/a24+2. They do not themselves require two distinct members of the strict-eight set to be nonzero. Cantor sum-squares likewise detect sums rather than the required simultaneous strict support. This is not an exhaustive search over all possible algebraic presentations or a global lower bound.

I inspected the incoming old324 projection data inertly. `direct/integer324/projected.json` is byte-identical to `direct/cap_cofinal_self/projected.json`: 38,181 bytes, SHA256 `1c23235590064c650cf7f41d158a7ec286e55edfa5036d5694c34ea054afee6f`. The projection certificate has SHA256 `c0516054893300d440c14cdae1ad63dccdeb56cddd6ad9f3113216dab3f1c784`. Its actual records say:

- v143 is retained at compact coordinate87.
- v140 is eliminated at step2, restored as v144+v145.
- v145 is retained at compact coordinate88.
- v144 is also eliminated, restored as `(v142+1)*v143`, which is quadratic.
- The unused N² gate v175 is eliminated at step119 as N².

Consequently fully substituting both old restorations into E_B makes it quadratic, and then multiplying it in (2) would exceed quadratic degree. A new quadratic projection may retain v140 or v144, choose another restoration, or change other retained variables. The five-definition presentation alone proves no net projected saving. In particular one cannot subtract two fresh coordinates from the old324 census. The old factored source also changes private square-difference witnesses; old-coordinate retention is a diagnostic, not a claim that its complete old projection certificate applies unchanged to the new source.

## 6. Separate optional Hstar private-slot reuse

There is a simple source-level alternative to adjoining a new Hstar coordinate. In the entire old body and guarded input, v175 occurs only at row158:

    v175-N^2=0.                                  (6)

It is neither a request port nor one of the 38 frame atoms, and has no guard or other consumer. Replace that private monic definition by

    v175-2-sum_(j=16)^24 v_j^2=0,                (7)

and use `baseBH=B*v175` at row382. No cofinal input or other old semantic port is repurposed. The variable name/metadata must explicitly change from its old private N² role if this option is implemented.

To compare it with the parent's fresh-Hstar presentation, distinguish the old private coordinate Nsq and the fresh Hstar coordinate. From a fresh-Hstar zero, discard Nsq=N² and rename Hstar to the reused slot. From a reused-slot zero, create a fresh Hstar with that value and restore Nsq=N². Every common nonprivate body/frame/request/guard coordinate is fixed. Moving the monic Hstar definition to row158 is an explicit row/namespace map; it does not assert the old value v175 is preserved. These are unique extensions for the respective monic definitions.

This option is independent of the weighted products. The old324 certificate already eliminated v175, so fresh Hstar followed by elimination of the orphan N² component may have the same projected dimension as this reuse. No numerical saving follows without a complete new source and projection audit.

The existing cofinal v0 or its root523 is not a substitute for the representative majorant under the retained proof. The nine CRT representatives are chosen after t,F,R0,K and their CRT moduli; no bound of their arbitrary permitted values by v0 is present. Changing t after their choice changes the factorial, beta and precision data. Reusing a private definition as in (7) avoids this cycle; assuming a new bound on a cofinal input would require a different architectural proof.

## 7. Verification boundary

The parent ordinary proof retains every18 request/54-port binding, all15 target norms, the positive cap, all38 frame atoms and the entire source131/C222 calibration. This addendum adds only the exact retained-row consequences (1), unique quadratic chain (2), strict-support argument (3)–(4), fresh private witness maps, and the separate optional monic-slot map (6)–(7). It does not delete another old support-pair graph, drop F's guard, change a power meaning or modify native coefficients.

A future held source must bind every whole changed row/coordinate/metadata map, the old and new consumer/guard privacy, all eleven quadratic remainder replacements, and both witness directions. Its factorization/projection/quartic coefficients and measurements require separate complete reviewed code and explicitly released checks. None is supplied here. No endpoint, compiler execution, numerical improvement or maintained-page change is claimed.
