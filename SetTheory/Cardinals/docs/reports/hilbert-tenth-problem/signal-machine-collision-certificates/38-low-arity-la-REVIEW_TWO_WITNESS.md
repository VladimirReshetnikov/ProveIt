# Independent static review of the two-witness compiler

4 October 2026.

**Verdict: PASS. No mathematical correction was found in the two-witness construction or its stated resource bounds.** The native theorem is self-contained. Its optional POWER composition remains conditional on the explicitly identified, previously audited constructive Pell dependency.

## Scope and method

This review read the complete `PROOF.md` draft, Sections 1–8, and the predecessor `independent-power12-audit-20261004/AUDIT.md` as inert text. The scope is the two-witness compiler, its resource accounting, and the substitution into the accepted twelve-leaf POWER composition. Any separately added one-witness appendix is outside this review.

All findings below are static mathematical checks. No counter interpreter, physical simulator, author/source script, upstream code, mathematical checker, or Lean was executed for this review. Only text reads and creation of this review file were performed. The proof's separate finite-evidence claims are not independently certified here. No predecessor file was modified.

## 1. Clipping, interpolation, domains, and uniqueness

The clipping argument is valid for both by-horizon and first-halt-exactly-horizon predicates. At every tested entry time `t<T`, a counter clipped from an initial value at least `T` remains at least `T-t>0`; the original differs by its unchanged initial offset along the common branch history. Initially smaller counters start equal. Thus induction preserves branches and control states through transition `T`, including loops. Equality of final counters is neither needed nor asserted.

With `K=T+1` and `c=(K-1)!`, the signed binomial basis has `ell_i(h)=c delta_ih` on `[1,K]`. Its sum is the constant `c`, since two degree-at-most-`K-1` polynomials agreeing at `K` nodes are identical. Consequently the tensor residual is exactly zero on accepted grid points and `c^2` on rejected ones, including the full and empty tables.

The five residuals recover their domains rather than assuming them. The two range products force `u,v` into `[1,K]`. From `A-u=r-1>=0` and `(r-1)(u-K)=0`, either `u<K` and `A=u`, or `u=K` and `A>=K`. Hence `u=min(A,K)`, and similarly for `v`. This uniquely fixes

    r=A-min(A,K)+1, s=B-min(B,K)+1.

Conversely that positive pair satisfies every residual exactly when the clipped point is accepted. The witness fiber is therefore a singleton or empty. The stated bounds `r<=A`, `s<=B` follow from `u,v>=1`. Strict positivity of the integer witnesses is essential; permitting zero slacks genuinely allows the wrong tail representative.

## 2. Exact degree and the two boundary cautions

For `K>=2`, the range residuals have degree `K`, the clipping residuals degree two, and the acceptance residual has degree `deg F_S`. Substitution by `A-r+1,B-s+1` preserves the latter: its highest homogeneous part is nonzero after setting `r=s=0`. Highest homogeneous squares cannot cancel over the reals. Thus, with `deg(0)=-infinity`,

    deg P=max(2K,4,2 deg F_S)<=4K-4=4T.

Empty and full tables give degree `2K`; every table at `T=1` gives degree four. For the singleton table `{(1,1)}`, the identity `F_S=c^2-ell_1(x)ell_1(y)` has nonzero top monomial `-x^(K-1)y^(K-1)`, proving degree `4T` for the squared-sum compiler.

The fixed two-zero-test program with an increment-only sink accepts exactly native input `(0,0)` from transition two onward. It therefore realizes that singleton table for every by-horizon `T>=2`.

Both important cautions are correctly handled in the draft:

- At `T=0`, the degree-two polynomial is explicitly a separate five-slot definition. Direct substitution into the generic clipping residuals would retain redundant degree-four squares. The separate full/empty polynomials have six/seven monomials and the claimed unique accepted witness pair.
- The fixed two-test program's exact-time table is empty after `T=2`. The proof does not extend its fixed-program sharpness claim to those exact-time tables. A delay chain establishes sharpness at each individual exact horizon using a horizon-dependent program.

## 3. Coefficients, support, and explicit costs

All norms in the proof correctly include the affine substitutions. Each factor `A-r-(i-1)` has norm `i+1`. With `B_K=(K+1)!` and `L_K=2^(K-1)B_K`, triangle and product bounds give range norms at most `B_K`, summed basis norms at most `L_K`, tensor norm at most `L_K^2`, and clipping norms at most `2(K+1)`. Therefore the stated ceiling

    ||P||_1 <= Q_K=L_K^4+2B_K^2+8(K+1)^2

is valid. Each coefficient magnitude fits `ceil(log2(Q_K+1))` bits, plus a sign bit. This is `O(K log(K+1))`, uniformly in the table.

The tensor square has pairwise degrees at most `2K-2` in `(A,r)` and `(B,s)`. Its possible monomials number at most `binom(2K,2)^2`. The remaining squares involve only one pair and have degree at most `2K`. Their two extra degree layers add at most `8K+2` monomials. Thus

    N_K=K^2(2K-1)^2+8K+2

is a valid support ceiling, including `K=2`. Every individual exponent is at most `2K`. Explicit fixed-field sparse records consequently need at most

    N_K [ceil(log2(Q_K+1))+1+4 ceil(log2(2K+1))]

bits, apart from their header, proving the claimed `O(K^5 log(K+1))` expanded-storage upper bound. The comparison with the predecessor is appropriately restricted to upper bounds, rather than instancewise lower bounds.

The displayed arithmetic circuit count also checks exactly. With `m=K^2-|S|`, at most `2K^2+m+5` multiplications and `2K+10+max(m-1,0)` additions/subtractions suffice. Hence `4K^2+2K+14` gates is a valid uniform ceiling. Integer constants are leaves; no division or hidden witness is needed. The stated factored encoding size and `O(K^5)` coefficient-generation operation bound are valid straightforward upper bounds. Neither gate counts nor integer-operation counts imply unit-cost bit complexity. Determining the acceptance table still costs up to `K^2 T` native transitions in the stated direct procedure.

## 4. Conditional POWER composition

The repeated five POWER residuals agree with the accepted audit specialized to base two, with its denominator `d=4` and its former expression `A` renamed `Z`. The rational-square integrality recovery, positive-sign argument using integer `q_alpha>=1`, and restoration of the eliminated positive coordinates match that audit. This review imports its constructive all-exponent theorem and infinite-fiber result; it does not claim a new proof or execution of the Pell dependency.

Replacing the predecessor's three compiler witnesses and six residuals by the present two and five gives exactly 28 positive witnesses, three external inputs, 31 total variables, and 17 residual slots. Outputs are already included in the module leaf counts. The gap equations and positive outputs force positive decoding denominators; decoded outputs, exponents, and compiler witnesses are unique whenever solutions exist. The complete fiber remains infinite because the accepted module progression changes retained leaves while fixing its index and output.

The degree-twenty coefficient-one monomial in the first module's `H2^2` is absent from all other residual squares. Therefore the exact composed degree is `max(20,deg P)`, with the stated upper bound and horizon-zero case. No optimality, unbounded-horizon, finite-fold, novelty, or additional physical claim follows from these checks.
