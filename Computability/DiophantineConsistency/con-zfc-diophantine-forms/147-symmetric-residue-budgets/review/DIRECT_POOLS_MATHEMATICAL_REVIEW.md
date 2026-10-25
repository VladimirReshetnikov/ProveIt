# Independent review: symmetric remainder pools and odd-square radix

**Disposition:** PASS for the new mathematical reductions and inspected literal compilation, relative to the explicitly inherited signed C222/CRT/Pell source and ordinary calibration proofs. No new end-to-end proof-assistant certificate or proof of consistency is claimed.

The review was performed separately from the author of `direct_work/build.py` and `direct_work/PROOF.md` in this AI-assisted workflow. It is not outside human peer review.

## Exact reviewed artifacts

The primary reviewed construction is `odd_three_pools`, together with its integral translation `odd_three_pools_centered`. Independent expansion gives:

| Endpoint | Variables | Quadratic rows | Degree | Collected terms | Height |
|---|---:|---:|---:|---:|---:|
| Parent centered direct equation | 282 | 192 | 4 | 5491 | 128446 |
| New centered odd-square / three-pool equation | 258 | 186 | 4 | 5319 | 128446 |
| New centered four-pool control | 261 | 185 | 4 | 5332 | 128446 |

Thus the principal inspected endpoint improves the matched parent in dimension, number of residuals and collected support, preserving degree and coefficient height. It is a comparison within this direct small-coefficient family, not a global quartic or variable-count record.

The inherited `guarded.json` was compared byte-for-byte against the actual file at `direct/strict_dimension/guarded.json` in the incoming Cofinal Anchors archive. SHA-256:

`c1a80140106a91997025501852b22526bc0072921f82f6b39d9a06cb07b26128`.

The copied `source_certificate.json` is the archive's `direct/strict_dimension/transform_certificate.json`, SHA-256:

`218e21b1843848a21c90b67b652865f0acfa5e72bafe353a9c5fc018e9db1c76`.

The archive itself is in ProveIt commit `e0c98c629bf10d30b695884f6b1d2ab361bdf513`. The source pin is not silently replaced by the older comparison pin inside the inherited archive.

## New proof: low-digit recognition

The critical issue is whether nonnegativity can be postponed without using an arithmetic conclusion that already depends on it. I read the inherited `ORIENTATION_FIRST_PROOF.md` and `STRICT_BUDGET_PROOF.md`. They orient both coordinates of every principal Pell pair, identify all requested signed indices, and recover the eighteen powers before using the eleven interval-product guards. The new transformation deletes those eleven rows only. Every frame, anchor, orientation row, power congruence, numerator row and linear remainder-bound row remains present.

At the pre-factorial stage one therefore has t>=16, F>=1, B>=F+1>=2, V0=(F^2+1)^t, y=V0(V0-1), x>=2+(t+1)y, all nine actual representatives nonnegative, and q=(BH0)^x with H0=1+their sum. The stored representatives minus one need not be nonnegative; the proof correctly uses actual representatives.

The potentially delicate derived-label estimate is valid even before the later argument that the encoded index is nonzero. Its inherited ledger gives h<=(n*+1)^ell, ell=2^22. Since n*+1<=2H0 and B>=2, h<=(BH0)^ell. The inequality y>=2^t(2^t-1)>ell, already for t=16, gives x>=ell*t+4. Thus every required derived low coefficient is at most q/16. Ordinary upper representatives satisfy the same bound using max(1,n), which handles n=0 and the constant coefficient. For the factorial upper F^2+t, B>F and t>=16 give F^2+t<=B^(t+1); the endpoint gives x>=t(t+1)+4. This establishes its low-coefficient bound without assuming F=t!.

For D=q^k and the genuine binomial low part rho, the coefficient bound yields 0<=rho<D/8. The new quadratic budget D^2-4 sum(r_i^2)-1=u^2+v^2+w(w+1) gives |r_i|<D/2 for every unrestricted integer solution. The retained numerator equations imply r_i=rho modulo D without any sign assumption on their other quotients. Hence |r_i-rho|<5D/8<D, proving equality and recovering both old interval signs. The factorial fixed point and CRT decoding occur only after that recovery.

For completeness, canonical residues satisfy the same bound. Four-pool groups contain at most five entries; the merged group contains seven after multiplying its two lower-level residues by q. In either case 4 sum(rho_i^2)<D^2, so the integer budget minus one is nonnegative and has the standard ternary representation. The merger's q-scaled product equations preserve recognition at each residue's original modulus. No approximate or finite numeric evidence substitutes for these unbounded inequalities.

## New proof: odd-square radix

Replacing the front sign graph for o by q=(2z+1)^2 is a restriction on witnesses, so preservation cannot be inferred from a mere coordinate substitution. The proof supplies both directions.

Soundness initially knows only q>=1. The unchanged Pell orientation is established using the signed square frame, without the removed front sign. Interpreting V0 at known positive exponent t and base F^2+1>=1 is legitimate; the base-one case is included. The two retained ceiling sign graphs imply F>=1 and B>F>=1. The genuine B^x request then forces x>=0, independently of q. The beta endpoints strengthen this to x>=2+(t+1)y. Since q+1>=2, the numerator requests force the nine actual representatives and the derived h to be nonnegative; h is nonzero from the semantic anchor. Now BH0>=2 and its power request gives q=(BH0)^x>=B^2>B, restoring o=q-B-1>=0. This order is acyclic, including the provisional case q=1.

Completeness uses admissible parity choices, not a false claim about every parent zero. With F=t!, y is even; all beta CRT moduli are odd, so an arbitrarily large even beta code x can be selected. Every factor 1+F^2/i is odd because F^2/i=F(F/i) is even; hence B and N=B^x are odd. Every independent representative can then have a prescribed parity modulo the odd CRT modulus N^2. The existing opposite-parity condition on a,b makes the semantic anchor even; a different representative can make the sum of all nine representatives even, making H0 odd. These are compatible conditions on different free parity choices. The usual bounded representative lifts and dominant-a lift are retained. Therefore (BH0)^x is an odd square and an integer z supplies the new row.

I found no circular bootstrap, hidden positive-index assumption, parity obstruction, or loss of cofinal completeness in these new arguments.

## Independent exact checks

`review_direct_pools.py` imports no producing compiler or inherited polynomial-algebra module. Its standard-library sparse arithmetic independently checks:

- the exact old source and metadata hashes;
- deletion of precisely the eleven interval-product guards, and optionally the one named front sign graph;
- retention of every other source row, each interval's linear bound and all original coordinates;
- the literal new group budgets, fresh auxiliary census, scale products and odd-square equation;
- the recorded inherited factorization patch and its exact source/target binding;
- all 216 monic polynomial restorations, every intermediate residual's degree, and the removal only of unused coordinates;
- all integral translation identities, including the centered endpoint;
- every collected coefficient, exact degree, variable occurrence, term count and height;
- rejection of an altered pool row even when its target hash is refreshed.

The primary run receipts are `DIRECT_POOLS_REVIEW.json` and `DIRECT_POOLS_REVIEW_OPTIMIZED.json`. The four-pool optimized control is `FOUR_POOLS_REVIEW_OPTIMIZED.json`. This checker's factorization review authenticates and replays the inherited patch; it does not present that patch's semantic identity as newly proved by hashing. The existing factorization theorem and the inherited logical/number-theoretic calibration remain explicit dependencies. The ordinary new proof and the finite algebra check have different roles and are not conflated.
