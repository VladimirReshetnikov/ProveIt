# Fixed-numeral padding boundaries at the complete84 source

This bounded proof-only checkpoint finds no complete arithmetic saving. It excludes two concrete outer-mask simplifications and a family of positive-coordinate rescalings, uniformly over the inherited modified75 powers-of-five compiler recipe and its permitted padding. It does not classify all valid compiler designs, all constant specializations, or circuits outside the interfaces stated below. The complete84 construction remains 47M+37A with eighteen positive witnesses; no global lower bound is claimed.

The parent source is `complete84_scaled_strong_output.json`, SHA-256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`. Its complete 84 rows were read as inert JSON. No saved source array, frozen helper, compiler or predecessor was executed or imported. All derivations below are exact elementary identities or consequences of the explicitly cited native theorem. No numerical sample is used.

## 1. Literal interface and recipe scope

Write `m=Bm1=B−1`, `V=2^b`, `B=V^L=2^d`, `d=bL`. The six fixed numeral ports are

```
m, Kconstant, 2d, b, MC, MF_source.
```

The literal source name of the last one is `MF`; throughout this note it means **the shifted source coefficient**, not the native field mask. Put `MFn=MF_native`. The fixed recipe gives

```
Kconstant=DC+B*DR,
MF_source=m+MFn,
0<MC<m, 0<MFn<m,
MC≡2 (mod 4), v2(MFn)=2.
```

The modification in `complete75_half_binomial_compiler.md` Section 1 is specifically `MC=MC0−2V^e*`, `MFn=MF0+4`, with an ignored dummy exponent `e*`. Its native support has Start at exponent 0, End at exponent 1, all other exponents positive, and maximum `Emax<L−1`. Consequently

```
Dmask=m−MC = sum_(e∈E, e≠1) V^e + 2V^e*.
```

Its base-V digits are at most 3, its unit digit is 1, and `V>=16`. In particular `Dmask<V^(Emax+1)<=V^(L−1)=B/V`. The recipe chooses b and L to be powers of five, with `2^b>=16`; thus b is divisible by 5, as is d. These restrictions concern the actual recipe, not arbitrary positive assignments to the six numeral ports.

For reference, the retained full source has `q=m*Jrep+1`, `X=w*q`, and `Y=s*q^3`. The inherited reductions from the asymmetric native construction to complete84 leave q, X and w unchanged. Their established full-positive-zero theorem gives, at every parent positive zero on an authentic slice,

```
q=2^t, X=2^R, w=2^(R−t), t>=4, R>3q.
```

This is an inherited soundness conclusion for the full zero set, not a canonical-completeness choice imposed on some selected solutions. The ordinary input is positive, all eighteen witnesses are strictly positive integers, and the fixed machine/recipe is independent of the input. Nothing below weakens those hypotheses.

## 2. The outer-mask bilinear remainder cannot vanish by recipe padding

The literal one-based rows 52–59 are

```
gap_product = repunit * q_minus_F
gap         = gap_product + q_minus_FZ
Lm1         = Lbig − 1
rproduct    = gap * Lm1
qMF         = q * MF_source
mask_factor = MC + qMF
mask        = mask_factor * Jrep
r_lhs       = rproduct + mask.
```

Here `repunit=m*Jrep=q−1`, `Lbig=q^2`, `q_minus_F=q−F`, and `q_minus_FZ=q−F−Z`. Therefore `g=gap=q(q−F)−Z`, and the actual packed index is

```
R = (q²−1)g + Jrep(MF_source*q+MC)
  = Jrep[ m(q+1)g + MF_source*q+MC ].                 (1)
```

The second identity uses the actual paid repunit relation; it is an all-ring identity and involves no division. The six rows 54–59 cost 3M+3A. Existing `complete84_cross_block_next.md` gives another six-row schedule, not a saving. The following statements address possible constant specializations of that boundary.

**Bilinear factor criterion.** For fixed nonzero rational m, the polynomial

`B(q,g)=m(q+1)g+M*q+C`

has a nonconstant factorization over the rationals if and only if `C=M`.

Indeed its coefficients as a degree-one polynomial in g are `m(q+1)` and `Mq+C`. They have a common nonconstant factor precisely when the latter vanishes at q=−1, namely when `C=M`. If they are coprime, Gauss's lemma and degree one in g give irreducibility in `Q[q,g]`. If `C=M`, the explicit factorization is `(q+1)(mg+M)`. Equivalently, its two-by-two bilinear coefficient determinant is `m(C−M)`.

This proves a factorization statement at the declared q,g interface, not a six-operation circuit lower bound with the additional paid q², q³ or other donor registers. These q,g values can indeed vary independently as formal coordinates at a fixed numeral slice: q varies through Jrep, and Z supplies arbitrary variation of g.

For the actual source, `C=MC<m<MF_source=M`, so `C=M` is impossible under every permitted padding. The counterfactual equality would give the five-row evaluation

```
u=m*g; v=u+M; a=q+1; b=a*v; R=Jrep*b,
```

costing 3M+2A. The other simple five-row case `C=−M` would give

```
a=q+1; b=a*g; c=M*Jrep; e=b+c; R=repunit*e,
```

also 3M+2A, but is excluded by positivity. Neither equality can be created by increasing b or L, adding ignored clauses/dummies, or taking either allowed high-monomial correction while retaining this recipe.

**Integer gap-translation criterion.** Put `g'=g+c` with a fixed integer c. Then (1) becomes

```
R = Jrep[ m(q+1)g' + (MF_source−mc)q + (MC−mc) ].     (2)
```

The q-dependent remainder disappears exactly when `m|MF_source`; the constant remainder disappears exactly when `m|MC`. Neither can happen: `0<MC<m`, and `MF_source≡MFn (mod m)` with `0<MFn<m`.

The first counterfactual is relevant to paid cost. If `MF_source=mc`, then

`R=(q²−1)(g+c)+(MC−MF_source)Jrep`

has a five-operation evaluation at paid q²,g,Jrep when the precomputed integer difference is allowed as a fixed numeral: two multiplications and three additions/subtractions. The recipe never supplies that divisibility. This is an algebraic/integrality obstruction even before any positivity or inverse-map issue for a coordinate change is considered. A rational shift `c=MF_source/m` is formally possible but is not an integer translation and supplies no positive-integer coordinate map. A redesigned rational or scaled whole circuit lies outside this conclusion.

## 3. Every inherited fixed numeral has an odd prime divisor

**Proposition.** On each authentic fixed recipe slice, none of the six fixed numeral ports is a power of two.

Proof:

1. `m=B−1` is odd and greater than one.
2. `MF_source=m+MFn` is odd and greater than one, since MFn is divisible by four and positive.
3. b and d are positive powers of five, and `2^b>=16` excludes b=1. Hence both b and 2d have an odd prime factor 5.
4. The displayed Dmask formula gives `Dmask≡1 (mod 4)` and therefore `MC≡2 (mod 4)`. Also `MC=m−Dmask>B−1−B/V>2` using the recipe's unused top positions. Thus MC has valuation exactly one and an odd factor greater than one.
5. Write a_tiles for the tile-alphabet size, to distinguish it from the Pell parameter. The literal fixed layout has

   `DC=V^(3a_tiles)+V^(H_layout+a_tiles)+V^(8M0)+V^(24M0)+sum_e c_e(V^(T1−e)+V^(T2−e))`,

   `DR=V^H_layout`, with the optional further positive high monomial in DC. Its unique lowest monomial is `V^(3a_tiles)`, of coefficient one; all other terms, including `B*DR`, have strictly higher exponent. Consequently

   `Kconstant=2^(3a_tiles*b) U`, with `U≡1 (mod 2^b)` and `U>1`.

   Thus Kconstant also has a nontrivial odd factor. The uniqueness of the lowest term and the absence of negative coefficients make this argument independent of possible carries among the higher terms. The exact valuation is also recorded in the accepted sparse-compiler note, Section 1.

This proves the proposition. It is uniform over the recipe's dummy-clause padding, strengthened radix choices and optional high term. It is not a theorem about every possible universal compiler.

**Dyadic-coordinate corollary.** Let

`P = m^e1 Kconstant^e2 (2d)^e3 b^e4 MC^e5 MF_source^e6`,

with nonnegative integer exponents, not all zero. At every parent positive zero, P does not divide w. Therefore the literal restriction/substitution

`old_w=P*new_w`, with `new_w` a positive integer,

retaining every other parent definition, leaves no positive zero on any authentic slice.

Each nontrivial monomial P has an odd prime divisor, whereas the inherited native theorem makes w a power of two. This proves both assertions. It excludes this specific way to absorb a fixed coefficient into the native dyadic scale; it does not exclude rescaling by a power of two, affine shifts, divisions with separately proved integrality, a re-encoded native kernel, or changes to other source equations. If the fixed language is empty the original zero set is already empty; for any language with an accepted input this proposed restriction destroys completeness.

## 4. Review remark 1 — the failed numeral-absorption proposal

The proposed sharing route was: “absorb the fixed transport coefficient into the main dyadic scale by writing `w=Kconstant*w_new`, so a numeral product might be reused elsewhere.” Retaining the actual source and a positive integer new witness makes this proposal false: Section 3 proves that Kconstant has an odd factor and hence cannot divide the native dyadic w at even one parent positive zero. The same failure applies to each of the other five full fixed-numeral ports and their nontrivial monomials. No gate saving is claimed from the rejected proposal.

Likewise the tempting equal-mask or integral gap-centering specializations in Section 2 are counterfactual recipes, not discovered compiler slices. Their five-gate schedules are retained only to explain the attempted savings and their exact obstructions. No undocumented restriction is imposed on the ordinary input or on which accepting histories must exist.

## 5. Pins, checked dependencies and limits

All names below are in `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`, except the two explicitly marked `../../1980/` proofs.

| Inert dependency | SHA-256 | Scope used |
|---|---|---|
| `complete84_scaled_strong_output.json` | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` | All 84 literal rows, six numeral ports and witness declarations read |
| `complete84_scaled_strong_output.md` | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` | Full note; unchanged positive-zero/interface inheritance |
| `complete84_cross_block_next.md` | `f528326b033473e288c20da5ceb72bfd4cd94198ecfea11bf54f758a0ab3d5d5` | Full note; earlier six-row tie and its restricted monomial bound |
| `complete75_half_binomial_compiler.md` | `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117` | Full note; exact masks, shift, padding and fixed recipe |
| `complete75_asymmetric_scale_tradeoffs.md` | `3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2` | Lines 1–108 and 215–260; full-positive-zero dyadic scale and inherited map |
| `complete83_outer_family_sparse_two_primary.md` | `bda0275af08ceaf1637b6bfa3ba8a8347205f5a674783cec7105ca263bf3fb97` | Lines 1–90; only Section 1 compiler census/lowest monomial used; no 83 soundness inference |
| `../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87` | Lines 1–90; powers-of-five recipe, masks, optional high term |
| `../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md` | `b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39` | Lines 75–120; literal DC/DR layout and support separation |

The actual-modulus and index/transport joint-boundary notes were also read to avoid treating their already closed cuts as open searches. None of those lower bounds is strengthened here. The new conclusions are the stated all-padding recipe obstructions, not global arithmetic-complexity bounds. Inherited native soundness is not reproved. No new full source, helper/receipt, numerical compiler instance or gigantic Pell witness is required for these direct identities and divisibility proofs. Repository and Git state were untouched.
