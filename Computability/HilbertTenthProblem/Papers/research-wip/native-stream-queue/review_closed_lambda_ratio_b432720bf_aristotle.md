# Bounded analytic review of closed-lambda Remark18.1

All four statements of the new Remark18.1 pass independent analytic review under their stated hypotheses and the displayed counting lemmas. No correction to those statements or their error estimate was found. This is a bounded review of the write-specific ratio result and its needed interfaces, not a full audit of either manuscript, its global count theorem, inverse expansion, LDP, literature claims or numerical experiments.

The source is immutable commit `b432720bf6e56d62688d12f20e4d8349b8edeeeb`, at `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a135501-closed-lambda-terms/article.tex`. The article blob is `e1ef15a22b4969934d9966b2d82a6fc661fb8d3b`, SHA256 `65e29dd975585d9bf540a64094491e365cc7a054cafdc8b35c8b5284e5ad9051` (132425 bytes,1434 lines). The main challenge is lines1317–1358. The receipt records every actual contextual read span, including the limited scope of incidental history/LDP text. The standing retention rule was read at this same commit in `docs/incoming/README.md`, lines426–440.

## 1. Domains and the finite upper inequality

The standing model fixes s in{0,1}, r=s+1 in{1,2}, N=n+1 and b=(N-u)/r-1. Admissible u is positive with N-u a positive multiple of r, so b is a nonnegative integer. The fixed-parameter count A(b,u) itself is independent of s. Every pair of integers u>=1,b>=0 occurs by setting n=u+rb+s, so the first two assertions genuinely cover all such pairs rather than only one parity class of n. The root-chain subclass gives A(b,u)>=C_b*u^(b+1)>0, making R and its logarithm well defined.

The imported uniform estimate is

    A(b,u)<=2u^2(u+1)(4u)^b exp(u/2+E),
    E=3*2^(1/3)*u*(1+b/u)^(1/3)*exp(-b/(3u)).

Dividing by C_b*u^(b+1), then applying C_b>=4^b/((2b+1)(b+1)), gives exactly

    0<=log R<=u/2+E+log(2u(u+1)(2b+1)(b+1)).             (1)

The factor u is correct after cancellation; no uncharged polynomial factor is lost. The boundary cases cause no problem: A(0,u)=u and A(b,1)=C_b give R=1.

The proposition's derivation from its height estimate was also checked locally. With d=u-h>0, dividing the height bound by(4u)^b exp(u/2) gives an exponent at most d[-alpha+log(2e^3(1+alpha))+3log(u/d)]. For v=d/u, the maximum of v(A-3log v) is3exp(A/3-1); this gives the stated E exactly. There are at most u heights, with prefactors2h<=2u and d+1<=u+1; h=u and b=0 are handled separately in the source. The selected height proof, reduced-tree constraints and shape-count interface were read, including why q<=u-h and why the restricted height evaluation never evaluates the unrestricted series beyond its radius. This local verification does not assert that every preceding global majorant lemma or all manuscript claims were audited.

## 2. Single-spine convolution and the lower inequality

The read recurrence gives B_(m,0)(x)=sum_k C_k*m^(k+1)*x^k. Restricting its positive recursion to a single abstraction spine gives L_u=B_(u,0)*Q_u with Q_u=product_(m=0)^(u-1)(1-4mx)^(-1/2). At rho=1/(4u), all factors of Q_u are finite and positive, including the trivial m=0 factor. Normalizing its nonnegative coefficients defines an actual probability law, not a formal probability notation.

The Catalan ratios C_(k+1)/(4C_k)<1 imply C_(b-j)>=4^(-j)C_b. Applying this term by term in the finite coefficient convolution gives

    R(b,u)>=Q_u(rho)*Pr(J<=b),
    Q_u(rho)=sqrt(u^u/u!).                              (2)

From the displayed probability generating function, independently differentiating each factor gives mean mu=u(H_u-1)/2 and variance (1/2)sum_(k=1)^(u-1)u(u-k)/k^2<=u^2. The empty sums at u=1 give the constant random variable0.

Concavity of log yields integral_(j-1)^j log x dx >=(log(j-1)+log j)/2 for j>=2. Summing gives log(u!)<=u log u-u+1+(log u)/2, also with equality at u=1 in the resulting bound. Consequently

    log Q_u(rho)>=u/2-1/2-(log u)/4.

For a>0 and b>=mu+a*u, the event J>b is contained in the centered upper-tail event at a*u. Cantelli's inequality gives Pr(J>b)<=sigma^2/(sigma^2+a^2u^2)<=1/(1+a^2), including variance zero. The source proves Cantelli by the elementary squared-variable Markov argument; its centered variable and positive threshold are correct. There is no strict/inclusive integer-endpoint mistake. Thus Pr(J<=b)>=1/(1+a^(-2)), and(2) gives exactly the second assertion.

## 3. Sequence limit and moving-saddle error

For assertion(3), the quantifiers matter: u tends to infinity, one fixed positive a works for the entire sequence eventually, and log(b+1)=o(u). Since H_u>=log(u+1), the lower-threshold condition forces alpha=b/u to infinity. Therefore E/u=3*2^(1/3)*(1+alpha)^(1/3)*exp(-alpha/3) tends to zero. The two logarithmic prefactors in(1) and(2) are o(u), and the fixed Cantelli loss divided by u vanishes. Squeezing proves log R/u ->1/2. This proof neither covers bounded alpha nor removes the stated lower-tail condition.

For assertion(4), N tends to infinity with fixed r in{1,2}. Put L=log N. The positive Lambert definition gives t+log t=log(4eN)-r/2, so t~L and u_*=N/t~N/L. The assumption (u-u_*)L/u_* ->0 implies u/u_* ->1 and

    N/u-N/u_*=t*(u_*-u)/u=o(1).

Thus alpha-alpha_*=o(1), where alpha_*=log(4u_*)/r-1/2-1/u_*. Also log u-log u_*=o(1). Using H_u<=1+log u gives

    alpha-(H_u-1)/2
      >=(1/r-1/2)log u_*+(log4)/r-1/2+o(1).             (3)

For r=2 the right side tends to log2-1/2>0; for r=1 it diverges positively. One may therefore use the same a0=(log2-1/2)/2 for all sufficiently large terms, with an onset depending on the sequence. The lower assertion gives log R-u/2>=-O(log u).

The upper error is exact at the stated order: alpha=log(4u_*)/r-1/2+o(1) implies exp(-alpha/3)=O(u^(-1/(3r))) and(1+alpha)^(1/3)=O((log u)^(1/3)). Hence

    E=O(u^(1-1/(3r))*(log u)^(1/3)).                    (4)

Because b<N and log N=O(log u), the prefactor logarithm in(1) is O(log u), absorbed by(4) for both allowed r. This establishes the full asymmetric error interval and the limiting ratio. Nearest admissible rounding has |u0-u_*|<=r/2 and relative quantity O(L^2/N), so the stated example is valid. The restriction r in{1,2} is essential to this particular lower-margin argument; the remark is not a theorem for arbitrary r.

At u~N/log N, the expression in(4) has order

    N^(1-1/(3r))*(log N)^(-2/3+1/(3r))=R_r(N).

The post-remark comparison with PartI's error scale is therefore correct. It is an upper bound, not a proved asymptotic size or coefficient of the residual.

## 4. Localization and retained boundaries

The remark's little-o relative saddle window is stronger than the full PartI localization window |u/u_*-1|<1/log N. In the latter, alpha-alpha_* is only O(1), and for r=2 it can approach magnitude1/2. That does not supply the fixed positive Cantelli margin used above. The new pointwise ratio result consequently cannot by itself replace global localization or reprove the full count theorem.

The two localization stages were read and their displayed estimates checked conditionally on the imported coarse majorant: outside[N/(2L),2N/L], the strictly concave coarse envelope loses order N; inside this interval, E=O(N^(1-1/(6r))*L^(-2/3))=o(N/L^2), while an offset at least u_*/L loses at least N/(32rL^2) in the improved envelope. The remaining narrow interval has alpha-alpha_*=O(1) and E=O(R_r(N)); summing at most N admissible terms costs O(log N). This explains precisely the extra global argument the new remark does not supply. The full coarse-majorant proof and the resulting global theorem are not newly certified here.

**Review remark 1 (finite values do not establish monotone decrease).** The write note at line1358 displays full-ratio values0.737,0.738,0.732, then says both displayed sequences "decrease slowly". The first two full-ratio values increase as printed; they cannot be described as a decreasing sequence. The displayed single-spine values0.576,0.568,0.559 do decrease. This is a narrow qualification of the prose description, not a contradiction of any of the four statements: those asymptotics assert no monotonicity. The values themselves were not recomputed or independently validated, and no numerical experiment was run. The author's stronger warning that these finite values neither confirm nor refute the rate remains appropriate.

**Open question 1 (remaining ratio frontier, credited to the delivered reports and the write).** The second-order term in log R-u/2 at the saddle, the bounded-alpha regime and sequences with alpha tending to infinity without a positive fixed margin above(H_u-1)/2 remain outside the argument. A lower-tail estimate for J beyond this Cantelli use, together with suitably uniform upper control, is missing. Effective constants/onsets, multiplicative equivalents and external priority/literature comparisons likewise are not inferred from this review. No new operational-universality or paid Diophantine compiler result follows from a counting estimate.

## 5. Read scope and execution boundary

Article spans actually read are187–230,272–354,398–630,1000–1034 and1240–1380, totaling536 lines. The main proof challenge covers Remark18.1 and the selected dependencies described above. Neighboring historical comparisons, LDP discussion and checker descriptions in those spans were read only for context; no external-paper verification, full LDP audit or checker/source audit is claimed. Search hits outside these spans were navigation only. The15-line retention rule at docs/incoming426–440 was read separately. The companion metadata authenticates the whole immutable files and each exact byte span.

All calculations here are handwritten analytic derivations. Fresh metadata reads may hash bytes and identify Git objects only. No supplied, archived, frozen or predecessor scientific helper was executed/imported; no saved scientific array was evaluated, no degree propagated, no numerical recurrence replayed, and no build or external literature search was performed. The inert source copy and review artifacts are under /tmp. Repository/Git and source files remain unchanged. Root owns integration and any editorial correction; Riemann's separate review owns publication/provenance authentication.
