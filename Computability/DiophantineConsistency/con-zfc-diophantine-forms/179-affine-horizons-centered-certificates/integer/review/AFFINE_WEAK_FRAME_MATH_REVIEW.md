# Independent review: affine horizon and strengthened weak frame

**Status:** the arithmetic argument is accepted for the selected clean215 source, with the exact finite binding in `CLEAN215_INDEPENDENT.json` and the final addendum below. The earlier `AFFINE_WEAK_FRAME215.json` authenticates only the superseded incoming-projection prototype. Do not transfer that old prototype hash to the selected source. This review is ordinary mathematics plus finite source checking, not a new formal-kernel replay.

## Scope and attribution

The intended delta is `t=8h`, growth base `d=t+2`, `F=d^t`, a weak frame `W=C+sum(u_j²)` on underlying **arithmetic** coordinates, and a strengthened terminal Pell frame at center `4W+1`. Fixed-base pooling is inherited from source158. The affine horizon, weak-frame affine majorant, difference orientation error, small-horizon arithmetic and parity construction are already explicit in source160 `proofs/FRAME_PROOF.md`; novelty is the stronger frame compatible with pooled powers and its new composed source, not those lemmas separately.

The final source may use the round21 strict `q=4z+1` architecture or the incoming projection architecture. Those have different noncircular bootstrap orders. The review below distinguishes them; neither may silently borrow the other's literal graph or sign premises.

## 1. Absolute-value frame bounds suffice with the stronger center

For integers a,u, `|a*u|<=u²+floor(a²/4)`. Hence an affine atom `L=c+sum a_j*u_j` satisfies

`|L|<=sum_(a_j!=0)u_j²+|c|+sum floor(a_j²/4)`.

Choose C strictly larger than every computed atom overhead. The entire retained base/index/output ledger, including the actual derived-label anchor and new growth base8h+2, then obeys `|atom|<W`. The squared underlying coordinates must not include private Pell/frame witnesses: completeness fixes the arithmetic first, chooses W, then fills those private witnesses.

The discarded assertion `atom²<W` is **not** automatically retained. In the superseded projection prototype the exact frame was40 plus43 underlying squares, not22; the cleaner final chart requires its own exact recount.

Put S=4W. The unchanged norm with changed ordinate/product rows is

`A²-( (S+1)²-1 ) U²=1`,  `U=S(2z-1)`.

Thus U is nonzero and divisible by S. Classification gives `|A|=X_l(S+1)` for l>0. Since `Y_l(S+1)=l modS`, S divides l, so

`|A|>=X_S(S+1)>S^S=(4W)^(4W)`.

In particular `|A-1|>4W³` for W>=22 (and in the examined prototype W>=40). This proves the enlarged center before any arithmetic sign or power interpretation. Conversely choose `U=Y_S(S+1)` and `A=X_S(S+1)`. Reduction of the recurrence modulo2S gives `Y_S(S+1)=S mod2S`, so U/S is odd and the required z is integral. The strengthened frame is therefore constructively complete.

## 2. Canonical orientation remains valid

Retain the whole cap/comparison/semantic-anchor construction, every abscissa error and the error at index t. Replace only

`(Y_(F+t)-F-t)²` by `(Y_(F+t)-Y_t-F)²`.

This is an invertible integer change in the pair of errors: once the retained t error vanishes, the difference error recovers the old F+t error. With signed classified residues, each unchanged ordinate error has absolute value below2W; the changed difference is below3W. For at most15 principal pairs the reduced nonnegative sum is below `65W²+60<4W³<|A-1|`. Divisibility by A-1 forces zero. The exceptional anchor ordinate of absolute value1 must still be handled first, exactly as source160 does; it yields a strictly positive small anchor error and contradiction, not a legal application of the nonexceptional comparison theorem.

The retained norm-row subtractions used by the existing Pell-difference chart do not invalidate this change: add the exact new-square-minus-old-square to the actual orientation residual while retaining its same norm-row identity. This identity must be checked in the final finite certificate.

## 3. Singleton and pooled powers under the weak frame

Let b=W-1 and let a nonzero integer base n and all m_i,k_i have absolute value at most b. Canonical signed Pell congruences and the unchanged two-row pool give divisibility of

`E=sum_i [m_i*n^b-n^(b+k_i)]²`

by `T=2An-n²-1`. Every exponent is nonnegative and, for r<=15,

`0<=E<=60*b^(4b)<(4W)^(4W)<|T|`.

The last inequality follows from `|T|>=2|A|-(W-1)²-1>|A|>(4W)^(4W)`. Therefore E=0. At |n|>=2 this gives k_i>=0 and exact integer powers; at n=±1 it gives only the signed unit-power value, as required. The same r=1 argument repairs the retained singleton congruence theorem under the weaker atom bounds: it must not simply be cited with its former square-frame premise.

The converse is unchanged: true powers imply each error is divisible by T, supplying integral pool quotients and both quadratic rows. This establishes zero-existence equivalence, not an arbitrary-tuple inverse of the old quotients.

## 4. Horizon zero and the genuine small case

For every integer h, `d=8h+2` has |d|>=2. The singleton growth certificate first forces t>=0 and F=d^t. If t=0, then F=1 and `y=F(2v+1)` is odd, without assuming its sign. The two endpoints give

`x=2+(y+1)u0`, `x=1+(y+1)ut`, hence `1=(y+1)(ut-u0)`,

an even-integer contradiction. Thus t is a positive multiple of8, so t>=8 and F>=(10)^8.

At t=8, `lcm(1,...,8)²=840²=705600<10^8`. For every other positive multiple of8, t>=16 and `lcm(1,...,t)²<=16^(t-1)<(t+2)^t`. The CRT selector radius R=F therefore remains valid. Also `F>(t+1)^t`, strengthening the Horn multiplicity separation estimate.

## 5. Signed beta bootstrap and local digit bound

For the selected **round21 strict chart**, q=4z+1 implies q!=0 and |q+1|>=2 before signs. Interpret the q+1 pool first: representatives and the true derived label are nonnegative, giving H>=2. The raw index equation then gives B!=0, so |BH|>=2. The singleton self-radix request gives x>=0. At x=0, the terminal endpoint forces `1+(t+1)y` to divide-1; this contradicts t>=8 and the nonzero multiple y of F>1. Thus x>=1 and |q|>=2; the q pool now forces y+1>=0 and hence y>=F. The endpoints imply

`x>=F+1`, `x>=2+(t+1)y>=2+9*10^8`.

For the **incoming projection chart**, the q+1 pool cannot be used first because there is no q=4z+1 source row. Instead use even C, even F and H=2 mod4 to derive odd nonzero B and |BH|>=2; exclude x=0 by the same endpoint argument, interpret q to recover y, obtain the large x lower bound, and only then license q+1. Both schedules are acyclic, but they are not interchangeable source claims.

The inherited shortcut `x>2^32` is not licensed at the new t=8. What is actually needed survives: with `R0=2+t+x+y+F<2x` and `E0=2^23`, one has `R0^E0<2^x`. Indeed x>2^29; if `2^s<=x<2^(s+1)`, s>=29, then `E0*log2(2x)<E0*(s+2)<2^s<=x`. The middle inequality starts with `2^23*31<2^29` and is preserved on incrementing s. Source160 already supplies this exact repair.

Signed centered-binomial recovery can now authenticate B before asserting q positive; after that the retained local range/CRT/Horn proof applies. The exceptional boundary y=F must still be excluded only after local row recovery by the zero-accumulator/final-one contradiction. No positivity may be assumed earlier.

## 6. Completeness

Choose t in the cofinal positive multiples of8 beyond all proof-tree parameters and labels. Here `v2(t+2)=1`, so `v2(F)=t>v2(t!)`; the odd part of t! can be absorbed in an arbitrarily large odd multiplier of F. The old square-multiplier witness remains a permissible special case of the new linear odd multiplier. Consequently y can remain an even multiple of t!, above every accumulator. Binomial B is odd because `v2(F)>floor(log2 t)` gives `v2(F+i)=v2(i)` for1<=i<=t.

For the strict chart, choose arbitrarily large even x in the beta-CRT class and retained odd H; then q=(BH)^x is1 modulo4. After all arithmetic coordinates are fixed, construct W and the stronger Pell frame, canonical principal/cap witnesses and pooled quotients. This closes the dependency order. No old packed witness or old-frame certificate is identified with a new one.

**Conclusion:** the unbounded arithmetic composition is sound with the explicit corrections above. Final acceptance additionally requires the author's final exact source/certificate replay, complete source closure and matched comparison to incoming216/quartic and215/degree10 alternatives. No new end-to-end formal-kernel claim is warranted.

## Final selected clean215 source addendum

The selected parent is the delivered round21 `integer/final/beta217/equation.json`, not incoming affine216. The independently checked new unoptimized source is `round22/integer/clean215/weak215/equation.json`, SHA256 `ce05820233eec60e0c7d09e73d31fcb1082b37ad777d35e4334dbd0ba97f788e`.

- The full atom ledger has35 affine forms and43 distinct underlying arithmetic coordinates. The largest affine overhead is21 at the actual semantic-anchor label; the growth base has overhead18. Thus the actual new frame is **W=22+sum of43 squares**. No private Pell, cap or frame witness enters this sum. In the parent, W occurs only in the three rows being replaced:94,95 and131. No hidden old-frame constraint survives.
- Every row of the new arithmetic/frame mutation is independently reconstructed, including the exact difference-error update, changed growth modulus and congruence, new horizon scaling and removal of the private old horizon square root. Complete raw coefficient arrays agree, not only sampled values.
- A second exact contraction introduces `Jprod=F*S` while retaining `K=F*Sprime` and removes private `p=1+F*b`, `r=1+F*(a-1)`. All p/r occurrences are among the replaced consumers and defining rows. New consumers61 and64 are their old consumers after these substitutions. New consumer65 is **old consumer65+Sprime*old row63**, after the substitutions; old row63 is retained. This identity is independently checked as a full polynomial identity. Thus old p/r restore polynomially and Jprod is uniquely F*S. The contraction is an integer zero-set bijection, with no division or sign premise. Its shared-product method is credited to existing Horn factorization work.
- The selected sparse endpoint, SHA256 `8b93d12f98688e88f65d983ce27c94010d5f03e2bd32ba5108d6f2a618ed4a0b`, has **215 unrestricted integers,152 rows,14,578 terms,height16,866,degree4**. Its one residual-basis operation and full quartic expansion were independently replayed.
- The lower-height endpoint, SHA256 `c2606109924205387d59511a53684da293c5e25c791b98fe02c9ae6b5f5d7239`, has **215 unrestricted integers,152 rows,34,700 terms,height4,512,degree4**. All431 residual-basis operations were replayed forward and backward, and every quartic coefficient was independently collected.

`check_clean215.py` imports no producer/checker. Both normal and optimized Python runs pass; every coordinate is live. These checks close the finite-source condition in the body of this review for these exact hashes. Future reserialization or source edits require new hash binding, not transfer of this receipt by filename.

The sparse215 point improves our former217 sparse point in variables,rows andterms at unchanged height, and it improves incoming Pooled Projection216/153/15,158/334,952 on all four direct-quartic metrics. The4,512-height variant is a support tradeoff, not an improvement in every metric over the old4,576-height217 point. Incoming Quotient's220/157/8,847/2,336 remains an independent lower-height/lower-support tradeoff. No worldwide or global optimum is claimed.

### Final release binding and proof-text acceptance

The final release under `round22/integer/final` reserializes metadata but preserves every selected coefficient, residual label, variable descriptor and coordinate order. `bind_clean215_final.py` independently verifies those equalities and recollects the complete final expansions; `CLEAN215_FINAL_BINDING.json` records the final equation/expansion/proof hashes. It also confirms that all99 files of the complete retained round21 integer release occur byte-identically in `inherited/Round21_Integer217.zip`, with no missing member.

The final `PROOF.md` was read in full. Its §§2–5 supply the strengthened frame, orientation exception, weak-frame singleton/pool estimate, acyclic strict-chart bootstrap, zero-horizon contradiction, exact t=8 bounds and fresh completeness construction reviewed above. One wording error was corrected before acceptance: actual canonical Pell errors need only be divisible by A-1; only their *reduced orientation errors* vanish. The corrected completeness paragraph now supplies the integral modified-pool quotient rather than falsely asserting that Y_k-k itself is zero. The source algebra was unchanged by this correction.

**Final decision: accepted as an ordinary mathematical construction, with independent complete finite-source/expansion binding.** The supplied final normal/optimized checks, frozen rebuild and independently parsed304 printed residuals also pass. No unresolved mathematical or source-metric issue remains in this reviewed215 branch. The inherited foundational calibration remains explicitly inherited, not newly kernel-replayed.
