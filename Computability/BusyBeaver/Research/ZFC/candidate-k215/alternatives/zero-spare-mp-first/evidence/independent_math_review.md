# Independent mathematical review: MP-first zero-spare composition

Reviewed on 2026-10-21:
- report_draft/sections/calibration.tex
- rho6/zero_mp_first/packet/PROOF.md
- The retained permuted_credit.md, transfer_compiler.md, and composite_transfer_review.md.

Verdict: no substantive mathematical defect found in the candidate-specific calibration argument. This review does not rerun or replace the physical runtime or exact-startup certificates.

## All-natural credit

The command recurrences use the correct MP=0, S=1 fields and the correct outer predecessor for positive continuations. R(r)=W(r-1) for r>0 is strictly descending. Induction gives length(R(r))<=r, so every prefix weighs at least -r.

The Cantor pullback lemma is valid because f enumerates consecutive blocks [0],[0,1],... . For q(r)=g(r)+1, every positive prefix is k+B(k-1); the intended invariant makes it nonnegative. On diagonal s>=2, the leading s-1 AX words collectively have weight >=9(s-1), and their individual prefixes satisfy the stated lower bounds. The following S loses at most s, and the following MP loses at most s. Their lower bounds 8s-9 and 7s-9 are valid, with 7s-9>0 for s>=2. The initial words MP,S,MP have total/minimum -1. Thus the infinite schedule beginning at candidate0 requires exactly one conservative theorem head, not merely one in a finite experiment.

Minor exposition improvement: state the q-prefix identity for k>=1, and explicitly give the joint diagonal invariant B(T_s)>=-1 together with B(j)+j>=0. The present draft's induction is correct but compressed at this closure step.

## Dirty initial AX

The virtual AX seed gives U=A=B=1 and C=0. Its gate is enabled, since 0 differs from both 1-valued parameters. The first seven logical rows are native axioms at arbitrary natural parameters. The dominated row L(1,1,0,1) satisfies U<=A. Therefore exactly the asserted eight heads are available without using theoremhood of incoming cache1.

Q_1(1)=4P(1,1)+2=18. The retained lower suffix is P(18,P(0,0))=P(18,0)=171. Neither the draft nor PROOF.md assumes that this suffix is theorem-valued. Eight safe heads minus maximum conservative debt1 leave seven permanently above171. Later AX commands see safe top/cache, and hence add ten safe heads. Composite S has only one net old-head pop; its internal temporary head is the theorem-valued old top, and both tests remain sound.

## Completeness and exact dependencies

The relevant strong compiler is the three-command transfer compiler at:
parent/reference/transfer-parent/proofs/transfer_compiler.md
Its contract is universal in arbitrary natural top and retained stack, with d=h=0. Its refutation suffix B_1;H succeeds under that contract. The initial AX shell resets d=h=0 regardless of retained data, so the arbitrary tail171 is not a completeness obstacle.

The two-guard refinement is justified separately by:
parent/reference/transfer-parent/proofs/composite_transfer_review.md
Nonhalting stores agree exactly with the single-guard transfer until the composite possibly halts earlier. The proof needs this early-halt refinement, not an assumption that the two guards are equal. Its additional gate-nonfalsity fact also supports the auxiliary exact-return claims.

The MP-first re-encoding and credit bridge are:
parent/proofs/permuted_credit.md, especially Sections1-6.
The fixed successful suffix is encoded using the actual MP0/S1 fields. The shell P(2,P(Y,P(1,R))) begins with AX(0;1,Y), dominates Y, and is therefore cofinal. The scheduler visits every natural successively and every nonhalting candidate drains. No fairness or positive-density hypothesis is hidden here.

Do not replace these citations by the older provenance/baseline_compiler_review.md alone: that file concerns the earlier four-command compiler and uses a P(3,...) shell. Its argument is historically relevant but is not the exact three-command dependency used by this new candidate.

## Scope

The conclusion still depends on the exact source identity, dirty AX match, arbitrary-natural append-zero physical theorem, and inherited numerical-calculus/ZFC comparison. Neither document claims to have independently rebuilt the last comparison in a proof-assistant kernel. Subject to those separately identified premises, the ordinary mathematical consistency equivalence is supported.
