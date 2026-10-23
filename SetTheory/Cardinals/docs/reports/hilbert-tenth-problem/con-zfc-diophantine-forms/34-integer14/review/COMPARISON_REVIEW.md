# Wave-4 comparison and synthesis opportunities

Repository pin: `8c6eec9d19ef80538c8e61ff6e0180040583446a`.
Comparison baseline: `ae3007ca4467011e0e051c84acb4a1dd13971b0e`.

## Scope and evidence

The current report tree contains seven packages, 24--30, replacing wave-3 packages 16--23. Placement `604b1416b5` extracted arrival `375cc6e3d7`. Package 30 is the previous local release. The repository README is an intake reconciliation, not an independent mathematical proof or execution receipt. Its removed duplicate-source paths must not be treated as mathematical failures of the original ZIPs.

This review reads all seven package entry documents, selected primary proofs, and ten defining circuit packets. `SOURCE_LEDGER.json` records 39 exact Git blobs and SHA-256 digests. The newly written `audit_counts.py` checks those blobs and independently counts live operations and variables in all ten packets, without importing or executing any upstream program. `COUNT_AUDIT.json` records the result. Degrees in that receipt are explicitly *reported degrees*, not independently certified degrees. The selected proofs establish the mechanisms described below; this review does not claim a fresh end-to-end formal proof of any inherited compiler.

## Comparative frontier

All operation counts charge binary addition, subtraction, and multiplication, including scalar multiplication; shared expressions are counted once. Fixed-coefficient construction is excluded. System comparisons may be free and therefore cannot be compared to residual-system counts without normalization.

| Package | Distinct contribution | Main figures |
|---|---|---|
| 24 integer24 | Three progressively tighter separating weights; odd-scale signed norm | positive12 degree1069/123ops,1073/121,1081/120; integer24 degree1936/167ops |
| 25 hybrid12 | Square-sum inner bound and smaller coherent coefficient layout | positive12 degree1081/116ops; radix B=2^(5^9),977220 raw coefficient bytes |
| 26 ratio12 | Ratio separation and signed extension; parity layout | positive12 degree1081/116ops; integer24 degree2432/163ops; shifted systems110 and157ops |
| 27 wave4 | Multivariate coefficient Hornerization and exact recipe folding; sharper Jones majorants; degree lowering at fixed system cost | positive Jones9 degree120764·5^33+368/1537ops; unchanged-original-polynomial evaluator1480ops; 59-op systems degrees12,10,8,6 |
| 28 compact norms | Two-root norm bound plus signed divisibility finalizer | positive12 degree1081/116ops; natural Jones9 degree93264·5^33+288/20547ops |
| 29 simpler forms | Coprime Pell stack, intersective divisibility, three-root finalizer | integer17 degree424296·5^33+53824/20607ops; positive12 degree1097/116ops |
| 30 quartic31 | Relation-aware register elimination; scalar trace/product norm; sharper absolute companion | positive12 degree1081/111ops; integer24 degree2240/165ops,25 degree920/131,26 degree214/123; positive quartic31; naturalJones9 degree120724·5^32+366/1840ops |

The nine-variable count and seventeen-integer count are not contradictory records: they have different domains. A shift converts nonnegative to positive variables but does not make a positive-domain equation valid over unrestricted integers.

Among moderate-degree twelve-positive products, 30 wins operation count, while 24 wins degree. Among moderate-degree 24-integer products, 24 wins degree, 26 wins operations, and 30 lies between. The enormous-degree integer17 construction wins only variable count. The old 67-operation equation remains relevant; no inspected wave-4 construction beats that metric. The old 15-variable systems and sextic/octic tradeoffs should not be declared dominated simply because no current package reproduces them.

## Exact synthesis opportunities

### 1. Coefficient-aware Jones evaluation is independent of the finalizer

Package27 writes t_j=B^(5^j),v_j=B^(5^nu-5^j), obtaining

    e(B)=t_nu [z h_4(t_nu,v_0,...,v_nu)
             + sum_alpha c_alpha t_nu^(4-|alpha|) product_j v_j^alpha_j].

The identities v_nu=1 and v_j=t_j^4 v_(j+1) avoid separate enormous-exponent chains. Recursive multivariate Horner evaluation reduces the correction sum. Folding exact equal coefficient *polynomials* and literal recipes then reduces 346 records to98 distinct recipes, of which only64 are nonliteral. The original index still includes every record; this is an evaluator optimization, not removal of coefficients.

This mechanism can be applied to package30's quartic31 and402 coefficient records, and to package29's signed17 base. It does not depend on the finalizer or any positive-domain root inequality. Aliasing must use exact symbolic recipe equality, not equality observed at sampled ports. Constants whose equality holds only for one authentic tuple require a separate certificate. This is the strongest low-risk combination opportunity.

### 2. Quartic31 and the signed/natural finalizers are orthogonal

Package30 reduces the parent witness parameter from32 to31. Jones's exponent parameter is therefore5^32, not5^33. Any finalizer that only uses the Jones ratio interface can be specialized after this reduction, provided the complete new index is reconstructed.

Package28's finalizer is a distinct degree improvement; package27's evaluation and coefficient folding can make it inexpensive. Package29's signed17 theorem is especially promising: its proof needs the explicit Jones ratio structure, not the old finalizer. Its seven-step coprime Pell stack encodes six nonnegative base coordinates and positive margin; h positivity is inferred, and i can be replaced by its absolute value once nonzero. Its intersective homogeneous polynomial simultaneously imposes divisibility and nonvanishing. Its three-root finalizer works for signed radicands through Galois automorphisms and separated root weights. None of those steps requires nu=32 beyond inherited index estimates, which must be checked for nu=31. Recomputing a coherent quartic31 index and reusing a cheap evaluator is thus a plausible dramatic degree/cost improvement with unchanged17 variables.

This is a proposed combination, not a certificate that the final rebinding or degree computation has already been completed.

### 3. Reuse the scalar trace/product norm evaluator with tighter weights

Package24's lowest-degree positive weight is

    M=I[2T+R(E+2(X+Y)+sq^2)ic].

Its proof obtains a sharper conjugate bound than the simpler k(I²+T²) weight of30. Package30's scalar trace/product evaluator computes the same relevant multiquadratic norm without the more expensive quadratic-ring expansion. Combining the weight theorem with a rewritten norm evaluator can improve the1069-degree form's operation count without introducing a new root-recovery argument. The carrier and outer weight must be retained consistently; equal degree is not evidence that two variants define the same polynomial.

Package29's quotient shift h_old=q+h strengthens weak bootstrap bounds while preserving completeness, but changes the polynomial and raises its displayed degree to1097. It should be treated as a separate proof mechanism rather than substituted silently into a comparison.

### 4. Smaller coefficients require one whole proved tuple

Packages25 and27 both have B=2^(5^9), but their K and MF differ, despite equal beta and MC bytes. Their ports cannot be mixed. Package25 supplies a dedicated smaller-layout proof; package27 explicitly calls the new tuple a semantic dependency to validate separately. The sensible route is to audit one complete tuple, its tile language and compiler interface, then recompute all four ports and every Jones index constant together. A smaller coefficient radix does not itself lower the Jones witness parameter nu.

### 5. Low-degree lifting

The positive quartic31 is an exact register elimination, not just a new circuit. Repeating the signed odd-scale guard lift after that elimination may remove another lifted register relative to the51-integer quartic. Which variables need positivity must be traced through the reconstruction of the eliminated G. A count from substituting domain maps alone is not a proof that signed spurious solutions are absent.

## Proof and packaging cautions

- Exact circuit counts and source hashes are finite audits, not the unbounded equivalence proof.
- Root recovery must use automorphisms of the actual splitting field. Independent sign flips cannot be assumed when radicands have dependent square classes.
- Nonnegative-variable and positive-variable shifts can save gates but do not establish an unrestricted-integer result.
- Product-unit finalizers need their parity exclusion of the unwanted negative unit. Pure norm equations alone are insufficient.
- The nine-variable coefficient recipes remain fixed finite recipes. Materialized four-port bytes and a materialized z do not mean y or every coefficient leaf has been materialized.
- Include explicit new-material attribution and licence, inherited Wade/K215 notices where relevant, and accurate local paths. Package30's positive README incorrectly points to a nonexistent local coefficients folder; its authoritative central binding is the correct reference.
- Prefer a portable verification driver that reads a pinned source manifest and reports missing intake-omitted copies clearly. A failure after repository deduplication is a packaging dependency issue, not automatically a theorem defect.

## Assessment

There is no unique 'simplest' entry without prioritizing variable count, domain, degree, operations, coefficient height, and proof size. The most defensible round-5 synthesis is a small Pareto family: a cheap twelve-positive form, a cheaper1069-degree alternative, a quartic lift, an optimized nine-positive form, and a sharply optimized signed17 form. The main new work should be exact proof-interface composition and coefficient-recipe sharing rather than inventing an unproved universal compression.
