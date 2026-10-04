# Report46 manuscript-specific independent audit: free83 nonextension

Date: 2026-10-04 UTC
Verdict: **PASS, with the Report45 source-level application now verified.**

## Binding and scope

This is a new review of the actual Report46 TeX, not merely a repetition of the earlier author-packet verdict. The reviewed proof sections carry labels `sec:smallnorm`, `sec:lattice`, and `sec:freeproof`. They were Sections 8–10 at review time; inserting an unrelated earlier section may renumber them without changing this verdict.

The byte-exact reviewed block begins at `\section{Small-norm descent for the free83 interface}` and ends immediately before `\section{Verification, reproducibility, and limitations}`. Its SHA256 is:

    0138013bfa57b573f23f727b44215d5e97bbd9e3128bfdd79389ef2155685201

The block is saved as `sections8-10.tex`. `REVIEW_PINS.json` also pins the exact theorem statement and adjacent scope prose, the Section7 Pell-classification and odd-polynomial dependencies, and the Section2 outer-interface definitions. These are the binding review targets; the whole-TeX hash in that file is only the observed snapshot, not an assertion that unrelated sections have reached final form.

The theorem proved is exactly: for A>=4 even, Delta=A^2-1, p>=2 even, c=psi_A(p), R odd, and retained product P5=1, no positive integers f,S,T,y satisfy the literal free83 auxiliary and strong equations with Na Ns=Delta. The intermediate V has no sign restriction. Delta need not be squarefree. This does not prove generic free83 ordinary-input soundness or rule out changing outer witnesses beyond that sector.

## Manuscript-specific mathematical checks

1. **Self-contained small-norm descent.** The manuscript correctly reproduces the norm-preserving transformation and its strict descent. In the negative case, the terminal inequality gives the lower bound H-1; in the positive-small-norm case, both transformed coordinates remain positive until reaching a diagonal solution. The negative equality classification correctly includes (v,y)=(0,1), the terminal point (2(H-1),2H-1), and every inverse iterate. No equality endpoint is dropped.

2. **S=1 and exhaustion of signs.** With Na Ns=Delta, both factors are nonzero divisors of Delta and have the same sign. S=1 gives the impossible divisor Ns=Delta f^2-1>1 coprime to Delta. Thus H=S^2>=4. For Na<0, the manuscript correctly simplifies the source proof using Ns<0, rather than importing unnecessary mixed-sign cases: f>=2 contradicts H-1<=Delta; f=1 gives Ns=-1,S=A,Na=-Delta. For Na>0, its two cases f>=2 and f=1 correctly prove Na<H; Ns=1 in the latter case would give A^2-S^2=2. Therefore every positive branch has Na=z^2 with z^2|Delta.

3. **Nonsquarefree lattice.** The manuscript's added proof of integer-unit generation is valid: dividing by the appropriate least-unit power preserves integer coordinates and norm one, and positivity follows from w>=1 and its conjugate w^{-1}. No unproved maximal-order unit claim is used. Parity gives an even fundamental first coordinate and an odd exponent e. The strong lattice and composition identity are transcribed correctly. The gcd argument works in the displayed quotient ring even at a reducible or repeated quadratic, and excludes every prime of b0. The example A=26, Delta=675, f=2, S=45 correctly exhibits why the larger lattice is necessary.

4. **Residue separation.** Reduction by 2m and reflection preserve index parity and yield representatives with indices in [0,m]. For m>=2, the inequality psi_a(m)+psi_a(m-1)<chi_a(m) rules out both a nonzero difference and a positive sum vanishing modulo chi_a(m). The m=1 and zero-representative endpoints are explicitly valid.

5. **Final normalization and contradiction.** Since z|b0, the strong equation for (zf,zS), combined with the gcd conclusion, forces z=1. The independently checked earlier Pell-classification and odd-polynomial lemmas then give the required odd auxiliary index and signed congruence. Multiplication by C_* uses no modular division. The resulting indices et_* and ep have opposite parity. In the negative branch, the equality orbit makes V even, while c(T-1)-R is odd. These arguments exhaust all nonzero factor signs and divisors.

There is no transcription defect, omitted S=1 case, hidden squarefree assumption, or scope broadening in the reviewed theorem/proof block.

## Report45 outer invariants: previous conditionality closed

I separately read both the delivered Report45 TeX and its included reconstructed `COUNTERFAMILY.md`, checked the relevant formulas directly, and verified their SHA256 values against Report45's release manifest. The inspected construction explicitly has:

- Branch A: p=4u, n=3u, R=6u-epsilon
- Branch B: p=20v, n=14v, R=28v-1
- Both CRT branches enforce Z=1 mod4. Since q=0 mod4, Q=-1 mod4, and the actual mask term is M=2 mod4, the actual packed R=(q^2-qF-Z)Q+M is 3 mod4
- The established positive scales give X=2^p, Y=2^y with y>=3t>=1875, hence A=Y(X+1)+2=2 mod4 and A>=4
- The restored main coefficient is exactly c=psi_A(p), with p positive and divisible by four
- The first/main/input norm values are 1; the literal index and transport factors are both epsilon. Thus P5=1 also in the branch where those two factors are -1

The five factor formulas agree with the retained free83 interface. Therefore every Report45 fixed outer tuple satisfies every nonextension hypothesis. The application is no longer conditional on an unavailable construction artifact.

The source inspected here is the newly pinned reconstructed Report45 packet. This audit does not claim byte identity between its reconstructed proof and the historical lost proof. The actual checked hashes are:

- Report45 TeX: d659f7f565bdbbfab39f8b0fea0d78178e864acceff3227987c2794b768ded46
- Reconstructed counterfamily proof: 690c5a1dc237bd53a9582bfbe01fcd8a176174e6b116089a1842532f83c1770b
- Pinned square/product82 source JSON: 7c029ad047c9db4652621334cb4c57d1781b5833dfac19de734ef0cb4c05fc7a

## Execution boundary

No upstream Python, saved arithmetic schedule, historic verifier, or compiler builder was executed. The only newly written script, included in this audit packet, extracts exact reviewed byte ranges and verifies hashes; it does not evaluate any source schedule. The verdict is a direct proof audit, not an inference from bounded tests. Unrelated height, analytic-expansion, numerical-replay, and PDF-layout claims are outside this review.

## 02:14 UTC addendum: late source-status reconciliation

**PASS for the revised adjacent scope paragraph.** The theorem statement, entire even-rank proof block, Section7 dependencies, and Section2 interface are byte-identical to the initial reviewed versions. Only the prose following the theorem changed within the bound theorem excerpt. Its current SHA256 is:

    c2f43cf1c618f50daffa90591eed36df40ea7093fd59b2aaf27106a454f2fa28

The new paragraph correctly reports the separately audited odd-prime-index construction at commit `8cf6239b6d805b08f106c7fe31ea4b5b46601722`: infinitely many full positive zeros at every positive ordinary input on every unchanged inherited valid fixed-program slice, using prime main ranks p=1 mod4. Its restrictions to this candidate and its inherited coefficient recipe match the pinned source proof and independent repository review. This result concerns different outer tuples and odd main ranks, so it does not weaken or conflict with the fixed-even-rank nonextension theorem.

I independently checked the paragraph's quantifiers and scope against the newly retrieved proof and repository review; this narrow recheck is not a replacement for their prime-equidistribution proof or the separate native independent audit. The parent also confirmed the native independent auditor's PASS. The current sources are in `/workspace/shared/free83-prime-collapse-independent-audit-20261004/source/`:

- `free_coefficient83_prime_outer_collapse.md`: SHA256 d49cfcb09c8e6f422a5922c00eaeb3f8a0759d9e1772899659db968d43205abb
- `review_free_coefficient83_prime_outer_collapse_math.md`: SHA256 2412a61d7bc9a5e7d385f162f4022a57278170ab317c892804a369c7308cee31

The initial audit, theorem excerpt, and pin receipt are preserved under `history/initial-review-0154/`. The older excerpt's statement that generic free83 ordinary-input soundness remained open is historical and superseded by the cited odd-prime-index collapse; it is not the current status. The current `theorem-free83.tex` and `REVIEW_PINS.json` bind the corrected prose. The even-rank proof-block SHA256 remains 0138013bfa57b573f23f727b44215d5e97bbd9e3128bfdd79389ef2155685201.
