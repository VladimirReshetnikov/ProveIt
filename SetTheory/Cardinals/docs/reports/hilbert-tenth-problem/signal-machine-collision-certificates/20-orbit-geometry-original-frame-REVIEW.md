# Independent review: original-frame complete-configuration first hits

**Verdict: the final primary `PROOF.md` is valid, conditional on Report29's normal form and timed-chart theorem.** Its SHA-256 is `385c455537ee7c4631fd5400918b57602bc08c26383fe71f99b3345791964a8f`. I audited that actual document, including its full statement, primary arguments, witness/residual counts, affine compiler, and boundary cases. Its integer-weight and quiescent-vacuum hypotheses are explicit. No blocking correction remains. This is not a new independent proof of the entire mass-four classification. The optional inverse-phase strengthening is excluded from this frozen primary review and reviewed separately in `OPTIONAL_REVIEW.md`.

## 1. Expanding case: no configuration can repeat

At corresponding section times T_n, the two marker coordinates L_n and R_n are actual occupied sites. The repeated finite mode fixes the transverse vector z, and

R_n − L_n = (x_0+nΔ)ν+z, with Δ>0 and ν≠0.

Consequently

diam(G^{T_n}(c)) ≥ ||R_n−L_n||∞ ≥ (x_0+nΔ)||ν||∞−||z||∞ → ∞.

The section times tend to infinity because every cycle has positive duration. Restoring F^{T_n}(c)=τ_{δT_n}G^{T_n}(c) preserves diameter. The argument uses neither a persistent identity for the two units nor distinguishable unit labels: their geometric roles at each section suffice. Their occupied coordinates are not merely virtual control markers.

If F^{t_1}(c)=F^{t_2}(c) for any t_1<t_2, determinism gives F^{t+p}(c)=F^t(c) for all t≥t_1, with p=t_2−t_1. The finitely many positioned configurations in that eventual period have bounded diameter, contradicting the section subsequence. This excludes prefix–prefix, prefix–tail, and tail–tail repeats alike. It is not necessary to prove that diameter is monotone or unbounded at every time. In fact, equivariance gives the stronger exclusion of repeats up to translation, although that strengthening is unnecessary here.

For Report29's timed polynomial C(t,X;w), set P(X;t,w)=C(t,X;w) and regard t as natural. At each reachable complete target there is one time and one old witness tuple; all other targets have no witness. That time is necessarily the first time. Reclassifying the variable changes neither the polynomial nor its ordinary total degree.

Thus the literal expanding bound is

W = B_ch+K+M_ch+1 ≤ 7B_ch+1 ≤ 168d³J+1, for d≥1,

where M_ch counts chart inequalities. Empty filtered chart families may use P=1 with no witnesses. The claim is one **natural witness tuple**, not one scalar variable.

## 2. Remaining alternatives: select the first time

For independent, whole translated-periodic, finite, and no-unit alternatives, the finite prefix and common-phase tail give affine original-frame site coordinates and affine time. Exact full-target equality is a finite Presburger predicate, including all labels and the exclusion of extra occupied sites. Therefore Occ(z,t) is Presburger, as is

Occ(z,t) and no s∈N with s<t and Occ(z,s).

The supplied first-visit compiler applies to its piecewise rational-affine first-time function. With its final disjoint-cell counts B,I,H,C_cong, no square lifts are needed, and internal time gives

W = B+I+2C_cong+1,    R = 2+I+H+2C_cong.

These are different counts from the raw chart bound above. Do not claim 7B_ch+1 for every alternative without a separate first-time chart/count analysis. Repeated configurations and all prefix/tail overlaps are handled by minimization. Merely forgetting time in the unmodified timed certificate would fail here, for example on a stationary nonempty configuration.

## 3. Encoding and boundary conditions

- The final primary statement retains all Report29 hypotheses explicitly: finite alphabet, positive integral nonvacuum weights, unique zero-weight vacuum, quiescence, **mass conservation**, fixed finite-dimensional deterministic translation-equivariant finite-radius CA, at most one weight-one symbol, and fixed finite input of mass at most four. Positive weights and a small initial mass alone do not imply the needed orbit bound.
- Report29 supplies both the fixed nonzero label-tuple interface and, in its whole-configuration/padding subsection, the single canonical target interface used in the final primary proof. The latter has an external count m, four coordinate slots and four label-code slots: 0≤m≤4; active sites are distinct and strictly lexicographically sorted; active labels are nonzero codes from the fixed alphabet; every inactive label and coordinate is zero. Label codes are not weights.
- This uniform **target-schema** extension is legitimate without extra chart witnesses: retain the full sorted chart family, append m, active label codes, and the padded slots as constant/coordinate outputs, then apply the same compiler. Sorting already supplies unique order even when labels coincide. Each chart's output is a valid canonical target, so malformed encodings are rejected. Do not simply sum label-specific polynomials or leave padding unconstrained.
- Positivity and conservation limit occupied sites to four, but weighted configurations may have fewer. All weight-two/three/four labels remain covered by the source classification; the expansion proof only needs its two actual unit markers. With no unit symbol the affine alternative applies. Labels of weight greater than four and mass-mismatched targets cannot occur.
- A positive-mass orbit cannot reach the empty configuration. Mass-zero input is the vacuum forever, so the empty complete target has first time zero; nonempty targets are impossible. Treat it directly or by the affine first-time compiler. A wholly zero pattern is a different observation and is not this case.
- Report29 assumes d≥1. The final primary proof correctly adds a separate d=0 paragraph: Z⁰ has one site, its finite-alphabet orbit is eventually periodic, and a finite table of reachable labels and first times gives the same quartic conclusion. The factor 24d³J must not be used at d=0.

## 4. Exact scope

The conclusion concerns exact, positioned **complete** finite configurations. It does not remove the frame restriction for visited sites or fixed-pattern anchors: those observations can recur during an expanding injective configuration orbit. No original-frame semilinearity or piecewise-quadratic first-time claim is needed or obtained by this primary shortcut for expanding complete targets. The separate optional strengthening is outside this review's scope.

For every fixed promised rule, dimension and input, the polynomial and finite witness arity are effectively obtained from the supplied normal form. This is not one fixed-arity polynomial accepting arbitrary rules or arbitrary initial inputs. No generic single-fold MRDP claim, efficiency bound, or novelty claim follows.

## Sources inspected read-only

- Final primary `PROOF.md`, all sections: SHA-256 `385c455537ee7c4631fd5400918b57602bc08c26383fe71f99b3345791964a8f`.

- Report29, `report29.tex`: sections “Finite control and one scalar gap,” “Termination and the complete orbit form,” “Alphabets with no unit symbol,” and Appendix “Canonical timed quartic certificates.” SHA-256: `1e4b9cb159801ce06d283a851ce2c47925610a27f7914d0ed8c8e3902874cedc`.
- Report29 timed companion, `scientific/timed/PROOF.md`, including its padded interface and compiler: SHA-256 `103fe38f7c6d941995e579d7d73dd42ab3836a012666ba16858b158ff698d4c5`.
- Canonical first-visit packet, `PROOF.md`: §§2–4, 6.2–6.5, and 7. SHA-256: `3247951ca7afa4d65bd3eb90d99bfb48fcb43dbf0eaa067c3e9380cdfbcebbda`.

No source release was edited. This review is an ordinary mathematical audit; no simulation or finite arithmetic test is needed for the deterministic no-repeat implication.
