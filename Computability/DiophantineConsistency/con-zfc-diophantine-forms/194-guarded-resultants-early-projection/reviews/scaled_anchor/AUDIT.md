# Independent audit: the scaled-dyadic 212-integer quartic

## Verdict and exact object

**PASS on the new mathematical delta and on every emitted residual and quartic
coefficient**, relative to the explicitly credited source173 ordinary
Pell/CRT/C222 calibration. No new end-to-end formal-kernel compilation is
claimed. Neither Con(ZFC) nor nonsolvability is asserted independently.

The audited endpoint has 212 unrestricted integer variables, 151 quadratic
rows, exact degree 4, 5,357 collected nonzero monomials, coefficient height
17,592,186,044,420, residual height 4,194,304, and 1,008 residual terms.
Every coordinate is live. The full independent checker imports no producer
module and uses exact integer arithmetic.

Current equation SHA-256:
`7eb5cb1cb2bb53208846ec0718caba3764509dfa5bbd49f907f7ae45fc96fcfa`.
Expansion SHA-256:
`e101caa28dac4a82a7cc095a81e40bed19bf94be42aaf3b559f60966ffc3c565`.

An earlier equation hash `cf2cd781...` differs **only** in the `schema`
metadata field. Replacing the new schema with its old value reproduces that
old hash exactly; see `metadata_rebinding.json`. The complete checks were
rerun against the current bytes, not merely carried over.

## 1. Independent finite verification

`independent_audit.py` separately constructs all changed polynomials from
their semantic formulas and compares all 152 staging rows. It verifies:

* Exactly rows 91, 92, 96, 97, 127, 128, and 141 change before optimization.
* The physical map is X=1+D w, Y=D z, Z=A z, D=2^20, and multiplying
  the divided norm row by D gives the full physical Pell norm exactly.
* The orientation is reconstructed from all thirteen other **actual**
  physical pairs, including both shifted-storage charts, rather than
  trusting the producer's listed edit. Adding back the thirteen ordinary
  norm rows yields their raw squared errors plus w²+(z-t)².
* The unchanged literal cap is exactly the cap with z² replacing the
  former physical growth ordinate square. No D² is hidden in the cap.
* All sixteen actual power requests, all 48 base/index/output ports, all
  35 ledger atoms, and the 30 framed coordinates match independently.
* All 79 integral coordinate/row operations replay forward, individually
  backward, and compositionally backward. The old private root appears
  in no other row; exactly its slot and row are deleted.
* Every resulting row and every collected coefficient of the sum of row
  squares agree, as do all dimensions, degrees, heights, and liveness.

Both normal Python and `python -O` pass. Six deliberate mutations (frame,
growth norm, orientation, cap, final row, expansion) are all rejected under
both modes: twelve rejections. There are also 1,064 signed modular
regressions at positive and negative odd centers, dyadic exponents 2 through
20, and signed/zero indices. These are regression tests, not substitutes
for the proofs below.

The producer's separate release verifier also passes **normally and under
`-O`, both with `--parent`**, against the producer-frozen equation bytes.
It checks all 151 plain-text and all 151 TeX residuals, freshly relocates
the whole input package, reconstructs seven byte-identical JSON outputs,
and runs the complete 26-stage original source replay. Receipts are
`package_receipt.json` and `package_receipt_optimized.json`.
An earlier transient printed-TeX parser failure (a regex replacement
introduced U+0001 and left a leading `{}`) was reported and corrected;
the final successful runs are after that correction. It was not a
coefficient mismatch. The original source verifier was also independently
invoked directly, rather than only through the new wrapper.

## 2. Weighted weak frame and all signed Pell cases

For every affine atom L=c+Σa_j u_j, the verified weights satisfy
|a_j|≤w_j and |c|≤2. Because |u|≤u² for integer u,

    |L| ≤ 2+Σw_j u_j² < W=22+Σw_j u_j².

In particular w_t=D and the half-C coordinate has weight 2. This is an
absolute atom bound, not a squared-atom bound. All coordinates in the
frame are arithmetic coordinates chosen before any private Pell witness.

The frame has S=4W, U=S(2v-1), V=(S+1)U, and A²+U²−V²=1.
Thus A is odd and U is nonzero. Pell classification at S+1 and
Y_j(S+1)≡j (mod S) give |j|≥S. Consequently
|A|>S^S, |A−1|>4W³, and |A|>D+1 already at W=22. Completeness uses
j=S and Y_S(S+1)≡S (mod 2S), so U/S is odd.

The reused C-anchor's unchanged comparison argument needs only
|Y_C|>|C| and Y_C≠0 from the cap. It excludes C=0 and proves the
absolute anchor index is |C| before recovering any arithmetic sign.
C=2c is even, hence nonzero C has |C|≥2; the ±1 boundary is impossible.
Every ordinary nonanchor index has magnitude <|C|.

For the scaled pair the cap gives |Y|=D|z|<D|Y_C|. At a=|A|,
Y_(c+1)(a)>aY_c(a)>D Y_c(a). Therefore its absolute index is at most
|C|, not necessarily strictly below it; this is sufficient because
|C|<W. No illicit strict bound was used.

For odd a, all Pell abscissae are odd, and Y_n(a)≡n (mod 2).
Writing a nonzero n=2^s m with m odd and repeatedly using
Y_(2m)=2X_mY_m proves v2(Y_n)=v2(n). Thus D|Y forces D|n.
The zero ordinate is treated separately as index zero. At an index
Dℓ, X_(Dℓ)(a)≡1 (mod D); the physical X≡1 (mod D) rules out its
negative, since D>2. This also rules out X=−1 at zero index.
For negative A, even-index abscissae agree with those at |A|, while the
ordinate sign is absorbed by signed ℓ. Thus the physical pair is a
canonical signed Pell pair at A, including A<0 and ℓ≤0.

The essential cancellation-free identities are

    Y_(Dℓ)/D = Y_ℓ Π_(j=0)^19 X_(2^jℓ),
    (X_(Dℓ)−1)/D
      = (D/2)(A²−1)(Y_(Dℓ/2)/(D/2))².

Their right sides are integer polynomials in A for each signed ℓ. Evaluation
at A=1 proves z≡ℓ and w≡0 modulo A−1, including negative A and ℓ=0.
There is **no cancellation of D modulo A−1**.

Reduce the pooled orientation modulo A−1 using these residues. Every
ordinate error has absolute residue <2W, and every other abscissa error
has absolute residue at most 2. The nonnegative residue sum is

    0 ≤ E < 56W²+56 < 4W³ < |A−1|.

It is divisible by A−1, hence zero. The ordinary pairs obtain their
canonical nominal indices and signs, while the scaled pair obtains ℓ=t,
so its physical index is Dt. No sign of t or any interpreted power has
been presumed in this reasoning.

## 3. Weak-frame powers, zero horizon, and arithmetic signs

At any nonzero framed base n, T=2An−n²−1 is nonzero and coprime to n.
With b=W−1, the retained singleton/pooled congruences give

    T | E=Σ(m_i n^b−n^(b+k_i))²,
    0≤E≤60 b^(4b)<(4W)^(4W)<|T|.

The index bounds make all exponents nonnegative. This estimate remains
valid for n=±1 and signed k_i. Hence E=0. For |n|≥2, negative k_i
would force an integer times a nontrivial power of n to equal 1; thus
k_i≥0 and m_i=n^k_i. At a unit base only the signed unit equality is
claimed. The physical scaled pair is covered by exactly this theorem.

For every integer t, d=4t+2 is nonzero and nonunit. Its request first
forces Dt≥0, so t≥0. At t=0 it forces F=1. Then y is odd and the
endpoints are x=2+(y+1)u0 and x=1+(y+1)ut: an even number would divide
1, impossible also when y=−1. Therefore t≥1 and F=d^(Dt)≥6^D>2^32.

The remaining bootstrap is noncircular. Bη=C+F+1 has odd right side, so
B≠0. Independently H=2+4(C+sum representatives) is 2 modulo 4, so
|BH|≥2. Its singleton forces x≥0; x=0 contradicts the last endpoint
because |y|≥F and t≥1. Thus |q|≥2. The q pool forces y+1≥0,
hence y≥F; the endpoints then give x≥F+1 and x≥2+(t+1)y.
Now |q+1|≥2, so its pool gives nonnegative actual representatives.
Only after that do the common remainder argument and first binomial
digit prove B=binom(F+t,t)>0, followed by q>0 and N>0.

The old short-digit inequalities remain strict at t=1 because F is
already enormous: F+t≤2F≤2^(F−1) and |q|≥2^((t+1)F+2).
The retained normalized-remainder guard authenticates all ten digits and
nine local range conditions. The y=F boundary is excluded only after
local-row recovery by positive-weight state propagation, as required.

## 4. All small horizons and local decoding

An initial proof draft wrongly reused a constructor-depth estimate at
T=t+2≥3 although the cited recurrence requires base at least 8. This was
identified and repaired before acceptance; no coefficient change was needed.

For t≥2, use d=4t+2≥10 as the comparison base. Each shell constructor on
integer arguments below s is <8s². Starting with leaves below d gives the
standard depth-r exponent e_r=2^(r+1)−1, so depth at most 19 gives
every label <d^(D−1). For t=1 the parameter leaves are zero and constant
leaves are at most one. Starting at s0=2, the recursive upper bound is

    s_r=8^(2^r−1)2^(2^r)=2^(4·2^r−3)
       <6^(2^(r+1)−1).

This establishes the same label bound at t=1. Thus L=d^D bounds every
label and L≥t, while F=L^t exactly. The source173 sharp separation lemma
allows that boundary: unequal factor counts force F+1≤L^t, impossible;
equal counts make coefficient differences strictly less than F because
both corresponding coefficients are positive. No strengthened F>L^t
assumption is silently required.

For every t≥1, Λ_t²≤16^(t−1)<F, so the every-row/every-prime selector
works, including t=1. The exact local degree ledger still gives exponent
2^23. With R0=2+t+x+y+F one has R0<3x and x>2^32; the dyadic estimate
2^23 log2(3x)<x then authenticates each local congruence as an exact row.
The inherited Horn-flow closure covers cycles and extracts a finite
shell-C222 refutation.

## 5. Cofinal completeness and source calibration

Choose t cofinally beyond a given finite proof tree and all local parameters.
Set d,K,F as above. Since v2(d)=1, v2(F)=Dt>v2(t!) and
v2(F+i)=v2(i) for 1≤i≤t, so B is odd. Odd square multiples permit
y=F a² to be arbitrarily large, satisfy t!|y, and satisfy the retained
odd-linear equation. The beta moduli are odd and pairwise coprime;
choose a sufficiently large positive beta code x before setting N=B^x.

Choose eight positive CRT representatives first. Since N² is odd,
choose C even and cofinally large in its prescribed class modulo N²,
above every other nominal index, including Dt. Only then choose H,q,
their genuine power outputs, and W. Neither N nor the earlier CRT
classes depends on this enlarged C. All framed arithmetic data precede
the private Pell choice, so there is no circular construction.

The positive fourfold frame supplies A. The doubling identities make the
scaled w,z integral and give the modified orientation quotient. Since
C exceeds every nominal index, the Pell growth gap leaves nonnegative
cap slack, even more so after replacing Y² by z². Every nonnegative
integer is r²+s²+v(v+1). The unchanged source173 even-C auxiliary
construction supplies the odd squared quotient and comparison CRT
witnesses. Genuine powers supply all remaining singleton/pool quotients.
The integral optimization chart and private deletion then give the literal
212-coordinate zero.

The complete original source173 ZIP was restored during the audit; an
initial placement-only archive could not run its verifier and was **not**
accepted as a complete closure. The final original ZIP has SHA-256
`760428ab91a1f39019ebb452d8b347235b5bb1a0935346e23de78b4542e68677`,
197 files, and 7,326,998 uncompressed bytes. Its affine213 stage is exactly
the new parent file (SHA `48b84f5c...`). Independent invocation of the
original verifier passes 196 manifest entries, 18 source pins, the
fourteen-source-expression depth certificate, and all 26 byte-identical
coefficient reconstruction stages. Full receipt: `source173_receipt.json`.

I read the original square-shell/Cantor recursive recoding argument and
the retained actual Lean source proof terms for
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Their composition
has the intended numerical-calculus meaning and does not run K215 or
specialize Jones. The freshness witness is reconstructed after recoding,
not transported by a false successor identity. This is an authenticated
inherited ordinary-proof calibration, **not** a fresh compilation or audit
of the complete transitive Lean import closure. The full C222-to-ZF bridge
remains the expressly credited logical dependency.

## 6. Fair comparison and stopping boundary

Against source173's optimized 213-variable companion, the new endpoint
strictly improves variables (213→212), rows (152→151), support
(5,402→5,357), and height (2,417,851,639,242,452,488,945,685→
17,592,186,044,420), retaining degree 4. This is not a comparison against
only a needlessly unoptimized parent.

Round22's 215-variable low-height endpoint remains a different tradeoff:
215 variables, 152 rows, 34,700 terms, height 4,512. The new endpoint is
smaller in variables/rows/support, not in height. No global minimum,
worldwide priority, machine-execution claim, or proof of consistency follows.

All audit changes are confined to `round23/review/scaled_anchor`; no old
source or upstream file and no remote state was modified by this audit.
