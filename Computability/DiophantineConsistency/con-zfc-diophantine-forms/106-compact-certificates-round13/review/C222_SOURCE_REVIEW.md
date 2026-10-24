# Source calibration review of the round-13 direct builder

The actual source function in `../direct/build_direct.py` matches the pinned numerical C222 calculus. The executable receipt `C222_SOURCE_CHECK.json` binds the reviewed builder SHA-256. Re-run `check_c222_source.py` if that builder changes; this receipt does not automatically cover later bytes.

## Exact finite source checks

The newly authored checker parses Python as data using `ast`, without importing or running either the new builder or any upstream program. A restricted expression normalizer alpha-renames local constructor arguments and expands their local assignment abbreviations. It proves the following are identical to the authenticated fixed-bound source `direct_calculus.py`:

* Nine constructor bodies: I, A, M, E, neg/N, X, req, clos, bundle.
* Nine actual axiom-code expressions, in order rho1, rho2, rho3, rho4, rho5, rho6, growG, rho8, bundle.

An independently authored sparse polynomial interpreter then evaluates those parsed expressions against the literal constructor-wire identities in `wire_eliminated_source.json`. A named wire is substituted only upon exact equality of every coefficient with its defining polynomial. All 56 named definitions are reached and matched. All twelve branch residual lists match exactly: truth, the nine axiom branches, mp and gen. Both normal Python and `-O` pass; there are no removable-assertion acceptance tests.

This is an exact compositional algebraic check rather than a finite sample or a claim about numerical agreement on small codes. The wire source SHA-256 is `1e7cf2f3ea9397e138c7543d47ccd00a967b8fbb2fd4c8d58f176c409033c1bb`, independently matched to the latest pinned Git blob.

## Read-only comparison with the retained Lean formulas

The retained `Code254.lean` defines P(x,y)=Cantor.toNat(x,y), hence 4P(x,y)=2(x+y)(x+y+1)+4y. The builder's I is exactly that ordinary integer polynomial. M=I+1, A=I+2 and E=I+3 agree with wel, wal and weq. The falsity code F is1, so neg(a)=I(a,1), and X(a,b)=neg(A(a,neg(b))) agrees with wex.

The displayed rho1 through rho6 and rho8 in Code254 agree with the parsed nine-code list. The seventh code is the newer `KCode222.growG`, namely I(E(c,a),I(E(c,b),A(M(a,b),E(a,b)))), not the obsolete rho7. The req and clos nesting, private label/matrix z,z in nks, membership vacuity vrel, and final negated helper-free bundle match KCode222's definitions literally under these constructor names.

The branch semantics also match KCode222.C222:

* truth sets p=q=v=0;
* an axiom sets p=q=0 and v equal to its code;
* mp imposes q=I(p,v), with p and q as its two premise codes;
* gen imposes q=0 and v=A(a,p), with p as its premise code;
* bundle additionally imposes ((c−a)(c−b))²=(d+1)².

Over nonnegative integers, the bundle equality forces both c≠a and c≠b. Conversely if both inequalities hold, d=|(c−a)(c−b)|−1 is a valid nonnegative witness. Thus the gating condition agrees exactly with the two inequality premises of the actual bundle constructor, including either ordering of the codes.

Each branch residual is squared; the product of their sums of squares vanishes exactly when at least one branch vanishes. The signed-pair arithmetic in the new function represents these ordinary differences without truncated subtraction. The accumulator factor is1+code(M0+1), unchanged. The changed short-beta range rows are intentionally not identical to the old range rows and remain the separate subject of the arithmetic/reconstruction audit.

## Semantic dependency, not a new formalization claim

The retained endpoint theorem is `KEndpoint.c222_iff_zf_refutation`; the next retained theorem is `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The chosen `Bridge.ConZFC` predicate is absence of a derivation of bottom from ZFCax_s. Those are inherited named source interfaces. The source constructor comparison above does not itself reprove their transitive Lean dependencies or emit a new object-ZFC derivation. The full direct arithmetic construction still needs the separately reviewed Horn-flow, bounded-trace, CRT, Pell, factorial/binomial and witness-reconstruction arguments.

No discrepancy was found in the actual new C222 code/source transcription. No upstream executable code or Lean was run.
