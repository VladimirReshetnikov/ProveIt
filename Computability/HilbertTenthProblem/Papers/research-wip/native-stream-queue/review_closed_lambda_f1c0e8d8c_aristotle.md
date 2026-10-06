# Bounded addendum: the explicit large-N lambda window correction

The new mathematical wording at immutable f1c0e8d8c44e985a980700e9cce7275fd2037669 passes this bounded independent hand challenge. The explicit large-N quantifier agrees with the unchanged proof of Proposition18.2; both retained small-N counterexamples are valid against a literal all-N interpretation. The exact upper-edge limit and the distinction between r=1 and r=2 are correct. The published entropy extension still uses unchanged valid interfaces.

This compares the entire README/article diff from24e36bc20f95ce4d8771c0c6bdc3d6d251a0725a. Within the report directory only README.md, article.tex and the PDF change. The PDF is byte-bound only. The reported numerical campaigns, builds and label/page checks remain reported claims, not newly verified evidence. Three previously identified editorial problems remain in the text and are retained below; no new mathematical defect was found in the inspected changes.

## 1. Large-N quantifier and the two retained boundary examples

Article1369 now explicitly states an N_0(r) and N>=N_0(r). The proof at1406–1415 already argues eventually, uses t~log N and u~N/log N, and selects K=1 only for large N. Its estimates give uniform constants across the displayed window for each fixed r=1,2. The explicit quantifier therefore states exactly the proved range.

For the two retained examples put(r,N,u)=(1,2,1) or(2,3,1). In either case b=(N-u)/r-1=0, and the exact boundary count A(0,u)=u gives R(0,1)=1. Thus log R-u/2=-1/2.

To check actual window membership rather than assume it, let t be the positive solution of

    t+log t=log(4eN)-r/2,  u*=N/t.

The left side is strictly increasing. Comparing at1 and2 gives1<t<2 in both cases: the two right sides are log8+1/2 and log12. Elementary integral bounds1/2<log2<3/4 and log3<7/6 suffice for these comparisons. Hence at(r,N)=(1,2),

    |u/u*-1|=1-t/2<1/2<1/log2,

and at(r,N)=(2,3),

    |u/u*-1|=1-t/3<2/3<1/log3.

They are admissible points in the actual open windows. An asserted lower bound -C_r*log u at every such point would give0<=-1/2, impossible for every finite C_r. These examples say nothing against the asymptotic bound for sufficiently large N.

**Review remark1 (retained quantifier correction).** README267–281 and article1418 preserve the former wording and the two examples rather than silently deleting them. This is a clarification of the finite domain of the displayed asymptotic statement. Earlier frozen reviews checked its large-N proof and did not establish an all-N extension; this addendum does not reclassify their bounded mathematical PASS as a defect. Big-O itself conventionally describes an eventual estimate, so the counterexamples target the explicitly universal finite reading, not the conventional asymptotic reading.

## 2. Exact edge margin and both size conventions

Let L=log N, t=N/u*, and use the exact saddle identity

    t=log(4u*)+1-r/2,  t/L ->1.

At the real upper boundary v=u*(1+1/L),

    N/v=t/(1+1/L)=t-1+o(1).

For integer admissible points approaching this boundary from below, the same formula holds. Choose the largest admissible integer strictly below v; its distance from v is at most r. It eventually lies inside the lower edge too because u*/L ->infinity. This bounded rounding changes N/u by O(N/(u*)^2)=O(L^2/N)=o(1), and log u=log u*+o(1). Therefore

    alpha=log(4u*)/r-1/2-1/r+o(1).

With gamma=lim_(n->infinity)(H_n-log n), the exact asymptotic margin is

    alpha-(H_u-1)/2
      =(1/r-1/2)log u*+(log4-1)/r-gamma/2+o(1).         (1)

For r=2 it tends to log2-1/2-gamma/2<0, as now printed at1369 and1418. Its negativity does not depend on decimal testing: convexity of1/x gives H_n-log n>=1/2+1/(2n), hence gamma>=1/2, while strict trapezoidal comparison on[1,2] gives log2<3/4. The exact expression is therefore negative. The printed decimal approximation is reported only.

For r=1 the leading term is(1/2)log u*, so the margin tends to infinity. This is uniform throughout the window: for fixed N>r, the expression

    (N/r-1)/u-1/r-(H_u-1)/2

is strictly decreasing with integer u, so its least admissible value lies nearest the upper edge and has the divergent estimate(1). Consequently Remark18.1(2) already applies with one fixed positive margin for every sufficiently large point in the r=1 window. For r=2 the admissible near-edge sequence has negative margin, so that old positive-margin hypothesis fails on part of the window for all large N, and the tilt is useful there.

In both conventions the near-edge sequence has(u-u*)L/u* ->1, not0. It therefore fails the narrower hypothesis of Remark18.1(4), regardless of r. The new prose correctly separates this geometric exclusion from the distinct question of whether Remark18.1(2) already covers the excluded points.

**Review remark2 (retained r1/r2 wording).** The former clause mentioned only r=2 when describing the narrower hypothesis's exclusion. The new clause and dated note preserve that wording and explain the two conventions separately. No change to the fixed-pair tilt inequality, its constants, or its proof is required.

## 3. Unchanged tilt proof and the entropy extension

A fresh immutable byte comparison confirms that article1372–1416, the entire Proposition18.2 proof, is identical between the two commits. The finite statement1361–1368 is likewise unchanged. The underlying upper estimate471–489, single-spine/mean/convolution interface494–529, Cantelli passage556–561, and ratio proof1311–1356 are byte-identical. This is text authentication, not evaluation of a program or numerical array.

The separate frozen entropy note `/tmp/closed_lambda_tilt_entropy_aristotle.md` (SHA2561162943b4a11ae8bef89b04b5331cdd22797fa38332d7dff5f08616802b8d86e) uses exactly these interfaces. It retains the exact tilt logarithms to obtain loss<=1/2 log binom(u+kappa,kappa), then proves log R/u->1/2 whenever u->infinity, alpha->infinity and log(b+1)=o(u). This revision changes none of those hypotheses or supporting identities. The entropy theorem remains a separately proved extension, not a claim that this upstream article has already incorporated it. The general bounded positive-alpha case and second-order terms remain outside it.

No broader acceptance is inferred from this comparison. In particular the new numerical test summaries at README315–331/article1485 are read as provenance prose only; their reported arrays, floating-point accuracies, extrema and OEIS comparisons were not recomputed or authenticated scientifically here.

## 4. Earlier editorial findings still present

**Review remark3 (inventory, inherited from Riemann).** README70–71 still calls Report110's files18=1+7+10. Its own literal list79–98 instead displays20 entries, including12 data entries87–98. This addendum checks that textual contradiction only; it does not repeat archive extraction or a complete file-inventory audit. The aggregate39 claim is not newly challenged here.

**Review remark4 (Rocq size definition, inherited from Riemann).** README418–419 and article170 still say neither development defines a size. At the same immutable commit, Computability/CombinatoryLogic/Coq/Lambda.v232–237 defines size recursively, with each variable, application and abstraction constructor contributing1. Thus the size-definition clause remains false. This does not assert that the report's counting/asymptotic theorems are formalized, and no Coq build or formal proof check was run.

**Review remark5 (the tilt test-range description, inherited from Riemann).** Article1418 still describes the entire range4kappa_K<=u<=600 as one where the lower bound does not follow from R>=1. At u=4kappa its right side is

    u/2-2kappa(1+log u)=-2kappa log(4kappa)<0,

so R>=1 already proves it. For the stated K=0,kappa=11 choose u=44,b=44^2=1936; b>=mu follows even from H_u<=u. This is a valid instance in the named u-range, independently of any numerical campaign. The error is the universal range description, not Proposition18.2 or its proof. Its persistence does not supply evidence about which test cells were actually evaluated.

## 5. Immutable binding and limits

The metadata companion pins both revisions' README/article/PDF blobs and byte hashes, the exact full diff, the selected source spans, and the same-commit Rocq text. The primary mathematical reads are the entire new45-line tilt proof, the changed statement and retained notes, the saddle/window and ratio definitions needed above, plus the full README/article diff. The three persistent findings are checked only in their displayed text/source interfaces. Earlier review scopes and frozen artifacts remain unchanged.

No supplied, committed, archived, frozen or predecessor helper was executed/imported; no source/scientific/coefficient arrays were evaluated, no degree propagated, no numerical campaign or build replayed. Only fresh immutable byte/diff/span authentication is permitted in this addendum. All new files remain under/tmp, and no repository/Git state was modified. Root independently read and passed this entire addendum, including both exact counterexamples, the edge/rounding proof, the asymptotic scope and all three retained editorial findings; no correction was requested. This pair freezes after that challenge and immutable byte/span authentication.
