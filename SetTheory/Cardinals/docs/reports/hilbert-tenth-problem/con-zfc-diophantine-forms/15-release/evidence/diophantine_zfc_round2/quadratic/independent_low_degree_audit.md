# Independent audit of the low-degree alternatives

## Verdict and scope

**PASS** for the literal arithmetic, variable counts, equation counts, exact degrees, normalized 34-to-25 positive-zero bijection, and ordinary 33-to-20 positive-zero bijection. The ordinary 33-variable alternative passes its algebraic checks and the reviewed transfer of the ordinary Pell-kernel argument to the Start-only setting, conditional on the same explicitly imported generic rank, signed auxiliary step-down, asymmetric-scale, and Start-only compiler theorems. This audit does not replace those theorems with a formal proof assistant certificate and does not verify Con(ZFC).

The audited fixed numerals are `Bm1`, `Kconstant`, `MC`, and the inherited **shifted** `MF`. They are not unknowns. They must be an admissible output of the specified Start-only compiler; arbitrary positive values are not covered by the semantic claim.

- Parent: `diophantine_zfc_encoding/start_only_quartic34.json`, SHA-256 `84bac06eb0366d57ebdfd887b61927a8468bba8b5ca0066996cbc6096ac1b524`.
- Ordinary quadratic alternative: `ordinary_quartic33.json`, SHA-256 `cff28dd7d3e1b3a7dc0b248e3a4d99cfe5fbf5b801cdd2c0bcbfd047f0ecb56e`.
- Normalized cubic alternative: `start_only_sextic25.json`, SHA-256 `26a4e17beeafb2f57cf0c868fc67f83d3c1580e72ab1287873bb56d8cf796763`.

All variables are strictly positive integers. Replacing each by a nonnegative variable plus one gives the explicitly claimed nonnegative formulation without changing the number of variables or the exact degree.

## 1. Independent arithmetic verification

`independent_sparse_audit.py` was independently written for this audit. It imports only Python standard-library modules. It parses polynomial expressions through a restricted AST visitor and stores exact integer-coefficient sparse multivariate polynomials. It does not import or execute any received construction, elimination, or source-verification script. Fixed coefficients are retained as distinct symbolic parameters of degree zero; consequently the identities are uniform in the compiler ports.

It checks:

1. Every one of the 25 parent factored equations against its expanded residual.
2. Exact variable inventories, uniqueness, liveness, all equation degrees, and both sum-of-squares degrees.
3. The 24 ordinary rows against the independently specified replacement of the parent rows.
4. The normalized-to-ordinary strong identity under `i_o=Delta*i_n`.
5. All 25 parent rows under an independently specified inverse coordinate substitution for the cubic system.
6. The sixteen surviving rows, their order, and all nine eliminated zero rows.
7. The first-root shear as an exact polynomial identity.
8. Preservation of both exact degrees after all positivity shifts.
9. Explicit constant-independent monomial coefficients proving the exact degrees.

Both normal Python and `python -O` executions pass; checks are not implemented with removable assert statements. Full results are in `independent_sparse_audit.json`.

The 33-variable system has 24 quadratic residuals. Its expanded sum of squares has 224 symbolic terms and exact degree four; the coefficient of `tau_root^4` is one. The 25-variable system has sixteen residuals of degrees

    2,3,3,2,3,2,2,3,2,3,2,3,3,2,3,3.

Its expanded sum of squares has 252 symbolic terms and exact degree six; the coefficient of `Baux^2 V^4` is one. Symbolic term counts are not claims of minimal arithmetic complexity.

## 2. The 25-variable system: exact positive-zero bijection

Write `q=Bm1*Jrep+1`, `k=eta+zeta`, `T=auxiliary_quotient`, and `z=transport_quotient`. The inverse lift to the parent is

    N=(L+1)q, X=wq, C2=c^2, K=D^2-1,
    G=(q-1)(q-F)+alpha, F2=f^2, V0=Tf-1,
    g=y_aux^2-V^2,
    P=E(c-eta)+k, tau_root=tau_tail+E(c-eta).

Under this substitution the parent residuals with 1-based indices

    2,3,7,10,12,15,18,19,21

vanish identically. All other residuals are exactly the printed sixteen residuals, with their given signs and order. This proves algebraic equivalence once positivity of the restored coordinates and the forward shear has been checked.

### Forward positivity

At a positive parent zero, `a-E=Ns>0` and `c-eta=k(a-E)>0`. Put `U=E(c-eta)>0`. The first norm is

    tau_root^2=U(U+k)+1>U^2.

Because `tau_root` and `U` are positive integers, `tau_tail=tau_root-U>0`. All other retained coordinates remain positive. No Pell classification or compiler theorem is needed for this direction.

### Reverse positivity

At a positive cubic zero, `L=q^2-1>0`, so `N=(L+1)q=q^3>0`. Its second residual gives `a-E=sN>0`; hence `c-eta=k(a-E)>0`. Therefore `X`, `C2`, `P`, and the restored `tau_root` are positive. The main norm gives

    K=D^2-1=Delta*c^2>0.

For `G`, put `C=q-F-alpha`. The transport equation is

    (Kconstant+w)C+(q-F)-z(q-1)=1.

If `C<=0`, its first term is nonpositive and its remaining expression is

    1-F-(z-1)(q-1)<=0,

contradicting the right side one. Thus `C>0`, `q-F=C+alpha>0`, and `G=(q-1)(q-F)+alpha>0`.

The retained strong equations imply

    I=i(D^2-1)=i*Delta*c^2,
    Baux=I^2=Delta(f^2-1),
    f^2=1+Delta*i^2*c^4.

Here `Delta=a^2+4a+3>0`. Also `c=k(a-E)+eta>=3`. It follows that `f>c^2>2c`, so `V0=Tf-1>0` and `Baux>1`.

Finally, the retained auxiliary equation gives

    (Baux-1)(y_aux^2-V^2)=V^2-1.

The coordinate `V` is already strictly positive. It cannot be one: from `V=c(Tf-1)-Rf^2` it satisfies `V=-c mod f`, whereas `0<c+1<f`. Thus `V>1`, and the displayed identity forces `g=y_aux^2-V^2>0`.

Every restored coordinate is therefore positive. The lift and projection are mutual inverses, including the root shear. This is a genuine positive-zero bijection with the normalized 34-variable parent, not merely an equivalence of existence predicates. The compiler is needed only afterward to identify that predicate with ZFC inconsistency.

## 3. The ordinary 33-variable system

This system removes `K` and its defining equation, replaces the parent main-norm pair by

    D^2-Delta*C2=1,

and replaces `I=iK` by `I=iC2`. It retains `C2=c^2`, `Baux=I^2`, and `Baux=Delta(F2-1)`.

All unchanged residuals agree exactly with the parent. In parent residual notation the new main residual is `r13-r10`. Under `i_o=Delta*i_n`, the new strong residual equals

    r22+i_n*r13.

Consequently every normalized parent solution gives an ordinary solution by discarding `K`, setting `i_o=Delta*i_n`, and retaining every other coordinate. This direction is a literal algebraic implication with an explicitly positive coordinate map.

The reverse direction is **not** asserted by dividing the supplied ordinary `i` by `Delta`. Such a division has not been justified and need not be part of the witness map. The ordinary system instead recovers the same accepted computation through the ordinary strong-rank theorem.

### Check of the Start-only adaptation

From the positive definitions one obtains

    q>=16, X=wq, Y=a-E=sq^3, E=XY, c=kY+eta,
    A=a+2, Delta=A^2-1, D^2-Delta*c^2=1.

The preceding direct transport argument proves `C>0`. With `F,alpha>0` this gives the same bounds on `G=(q-1)(q-F)+alpha` as in the Start-only certificate. The inherited admissible-mask estimates therefore give

    (2q-1)(q^2-1)<R<q^4-q^3, E>=q^4>R+2.

The first and main norms give indices `n,p` with

    k=2*psi_(2XY^2+1)(n), c=psi_A(p).

The index equation has positive sign already: `k=R+1+hE`. As in the ordinary proof, the congruence `2n=R+1 mod E`, the index bounds, and `2XY^2+1>A` imply `p>n>=24`. The elementary Pell growth argument then gives

    c>A*Delta^2, c>2p, c>2R.

The ordinary strong equality is exactly

    (i*c^2)^2=Delta*(f^2-1).

This is precisely the premise of the generic relaxed strong-rank theorem, yielding

    f=chi_A(m), p|m, c|m, i*c^2=Delta*psi_A(m), m>=c>2p.

In particular the required integrality is justified, not guessed by cancellation:

    f^2-1=Delta*psi_A(m)^2=i*c^2*psi_A(m),

so `c^2` divides `f^2-1`. The ordinary inequality also gives `f>c^2/sqrt(Delta)>2c`. Define

    o=cT-Rf,
    j=Tf-1-R*(f^2-1)/c.

Both are integers, and `of=V+c>0`, `jc=V+R>0`. Thus `o,j>0`. In this low-degree system `V` is already a positive coordinate, so the more elaborate positivity restoration used in the ordinary product proof is not an additional unproved premise.

The retained auxiliary norm, these positive auxiliary coordinates, the rank conclusion, and `0<p,R<c/2` meet the same signed step-down lemma hypotheses, giving `p=R`. The no-wrap argument gives `2n=R+1`. The unchanged asymmetric-scale argument gives `X=2^R`. From this point the Start-only population, transport, and finite-window decoder applies unchanged: there is no input-marker restoration to perform. The fixed ZFC recognizer is the same one used in the parent.

Thus ordinary soundness needs the generic ordinary rank and compiler proof, not a normalized reverse coordinate identity. Completeness follows from the explicit normalized-to-ordinary map above.

## 4. Remaining imported theorem boundary

This audit reads and uses the ordinary transfer argument in `review/02-system63/FIXED_INPUT75_ORDINARY_PROOF.md`, the exact generic ordinary-rank statement quoted in `review/06-blank67/proofs/pell_lemma_audit.md`, the Start-only semantic argument in `review/06-blank67/proofs/fixed_blank_67_proof.md`, and the index bounds in `diophantine_zfc_review/START_ONLY_DEGREE_CERTIFICATE.md`.

It is important not to conflate the layers:

- The sparse checks establish exact algebra and uniform degree bounds.
- Section 2 establishes the positive-coordinate bijection for the sextic alternative.
- Section 3 checks that the ordinary theorem's hypotheses survive in the Start-only quadratic alternative.
- The inherited full compiler theorem and the fixed recognizer-to-`Con(ZFC)` bridge establish the final logical interpretation.

No global minimality claim follows. The initial two constructions are different tradeoffs: 33 variables and degree four versus 25 variables and degree six. Section 5 audits the subsequent 20-variable degree-eight alternative.

## 5. Further 20-variable octic alternative

`ordinary_octic20.json`, SHA-256 `9db5e80c2f77033e4a22022b3f95d1c78a2cbb52b7f11237a6604a347c4938f9`, also passes the independent sparse audit. All thirteen sequential elimination steps are verified against the actual solved equation at the stated current-list index. Each deleted equation equals the solved-variable residual up to sign, and substitution into every surviving row gives the next list. The final list is exactly the printed eleven equations.

Separately, without relying on that trace, the verifier applies this closed-form inverse to all 24 ordinary33 residuals:

    q=Bm1*Jrep+1, k=eta+zeta, H=4a+3,
    N=q^3, C2=c^2, G=(q-1)(q-F)+alpha,
    F2=f^2, V0=Tf-1, g=y_aux^2-V^2, Baux=I^2,
    P=E(c-eta)+k, X=wq, L=q^2-1,
    R=k-1-hE, Delta=a^2+H, D=wq+ac+gamma*H.

Exactly thirteen parent rows become identically zero. The remaining parent rows, with 1-based indices

    4,5,6,8,12,15,16,19,21,23,24,

are exactly the eleven final residuals. Their degrees are

    4,3,2,4,4,4,2,4,3,4,4.

The sum of squares has 390 symbolic terms and exact degree eight. Independently of all fixed coefficient values, its `E^4*c^4` coefficient is one. The positivity shifts preserve that degree.

### Positive inverse, without circular use of the ordinary theorem

The final equations give `a-E=sq^3>0` and `c-eta=k(a-E)>0`, so `N`, `X`, `L`, `C2`, `P`, `Delta`, and `D` are positive. The unchanged transport equation proves `C=q-F-alpha>0` by the same sign argument as above, and hence `G>0`. Although the initial definition `R=k-1-hE` does not visibly have positive sign, the retained packing equation also gives

    R=G(q^2-1)+(MC+q*MF)Jrep>0.

This is the required noncircular positivity justification for the eliminated index.

Before attempting to restore `g` or invoke ordinary33 soundness, these identities already meet the pre-rank first/main norm and mask-bound hypotheses of Section 3. They give `c>A*Delta^2` and therefore, from `I=i*c^2` and `I^2=Delta(f^2-1)`,

    f>c^2/sqrt(Delta)>2c.

Thus `F2>0`, `V0=Tf-1>0`, and `Baux=I^2>1`. The coordinate `V` is retained positive. Its congruence `V=-c mod f` and `0<c+1<f` exclude `V=1`. The auxiliary norm consequently forces

    g=(V^2-1)/(Baux-1)=y_aux^2-V^2>0.

All thirteen restored coordinates are positive, and all equalities have already been verified. This yields an exact positive-zero bijection with ordinary33. The positivity argument uses the elementary Pell bootstrap already needed by ordinary33, but it does not invoke the full ordinary33 semantic conclusion to manufacture its own missing hypotheses.

The parent `LOW_DEGREE_PROOF.md` was also reviewed. Its literal displayed systems and principal arguments agree with these checks. The exact sextic degree witness stated there is valid, and this audit additionally supplies the simpler constant-independent witness `Baux^2*V^4`.

The certified three-way tradeoff is therefore:

- 33 positive variables, 24 quadratic equations, one quartic.
- 25 positive variables, 16 cubic equations, one sextic.
- 20 positive variables, 11 quartic-or-lower equations, one octic.

The last option inherits ordinary33's named theorem dependencies; it introduces no new compiler or generic rank theorem.
