# The actual index/transport product needs nine gates at its paid cut

This bounded scout finds no smaller complete source. It proves a new exact-product obstruction outside the protected six-port finalizer: the actual index and transport factors, evaluated jointly from the nine paid coordinates specified below, require at least **4 multiplications and 5 additions/subtractions**. Their present joint cost is exactly nine operations. This does not exclude a replacement that uses extra source donors, changes supplied coordinates, or preserves only the complete positive zero set.

## 1. Actual source and the selected interface

The inert parent is `complete84_scaled_strong_output.json`, SHA-256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`. Its complete 84 rows and all supplied-port declarations were read as data; no array was evaluated. The inherited proof is `complete84_scaled_strong_output.md`, SHA-256 `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`.

Use the following actual paid cut:

| Symbol | Actual register or supplied port |
|---|---|
| k | `R10b` |
| R | `r_lhs` |
| E | `UM` |
| h | `h` |
| w | `w` |
| C | `marked_rhs` |
| U | `q_minus_F` |
| t | `transport_quotient` |
| r | `repunit` |

The only additional input is the fixed nonzero scalar `K=Kconstant`; every authentic compiler has K>0. The two factors and their product are

    N = k-R-hE,
    T = (K+w)C+U-tr,
    J = N*T.                                               (1)

The name J here denotes this joint factor, not the source's repunit witness `Jrep`. No new supplied quantity is introduced.

The exact parent rows are

    hpm1             = h*UM
    index_difference = R10b-hpm1
    norm_index       = index_difference-r_lhs
    kinner           = Kconstant+w
    innerC           = kinner*marked_rhs
    transport_partial= innerC+q_minus_F
    local_rhs        = transport_quotient*repunit
    norm_transport   = transport_partial-local_rhs.

These cost 3M+5A, and forming their product costs one more multiplication. All six private intermediates in this list have only their displayed next consumer. The two factor outputs are consumed only by `norm_product` and `all_units`. Associating those two finalizer products as `joint=norm_index*norm_transport` and `all_units=norm_four*joint` preserves both their count and the entire polynomial. Thus a joint evaluator with fewer than nine operations at this cut would save a complete gate; the theorem below excludes exactly that route.

All upstream producers and other downstream consumers remain paid. The theorem does not give `q`, `F`, `Z`, `s`, the individual products `hE`, `wC` or `tr`, or any further original register as extra free inputs.

## 2. These are genuinely independent source coordinates

Fix an authentic numeral tuple, and write m=`Bm1`>0 and ell=`twice_cell_bits`. Hold the ordinary input x and the supplied eta fixed as exterior parameters. Source identities give

    r=m*Jrep,                 q=r+1,
    U=q-F,                    E=w*s*q^4,
    R=(qU-Z)(q^2-1)+(MC+q*MF)*Jrep,
    C=U-Z-alpha-ell*x,        k=eta+zeta.                 (2)

The source MF is its shifted supplied numeral; no native-mask substitution is made. On the nonempty generic locus where w*q*(q^2-1) is nonzero, equations (2) have the rational inverse

    Jrep = r/m,
    F = q-U,
    Z = qU + ((MC+q*MF)*r/m-R)/(q^2-1),
    alpha = U-Z-ell*x-C,
    s = E/(w*q^4),
    zeta = k-eta,

with h,w,t unchanged. Consequently the nine formal cut values are algebraically independent over the characteristic-zero coefficient field of fixed exterior parameters. The denominators are used only to prove independence, never as source gates or as a positive-witness reconstruction.

In particular, the source relation E=XY does not make E dependent on the other eight cut values: the supplied scale s remains available in its upstream definition. Likewise R remains independently variable through Z once r and U are fixed. This is a source-specific independent cut, rather than a lower bound obtained by silently forgetting an algebraic relation.

## 3. Five additions are necessary

**Support lemma.** A division-free circuit starting from variables and scalar constants, using at most a additions/subtractions and any number of multiplications, produces a nonzero polynomial whose support has affine dimension at most a.

To see this, maintain one vector space V containing all support differences of every wire. Initially every nonzero wire is a monomial, so V=0 works; each wire's support lies in its own translate of V. A product still has support inside a translate of the same V. Adding or subtracting two wires requires at most one extra direction, the difference between their chosen support representatives. Cancellation only removes support points. Thus each addition increases the allowed dimension by at most one. Zero wires cause no difficulty and can be omitted.

The twelve terms of (1) are distinct when K is nonzero. In particular its support contains

    kC, RC, hEC, kwC, kU, ktr.

Relative to kC, the five support differences are

    R-k, h+E-k, w, U-C, t+r-C.                            (3)

Here the symbols in (3) denote exponent-basis vectors. These five vectors are independent: projection to the exponent coordinates R,h,w,U,t gives the 5-by-5 identity matrix. Hence the support has affine dimension at least five, and every circuit computing J needs at least five additions/subtractions. This allows any number of products, scalar constants and scalar multiplications. The concrete schedule already shows that five suffice.

## 4. Four multiplications are necessary

Give all affine operations and scalar multiplications for free. Count only multiplication gates with two nonconstant operands; this relaxation can only make the lower bound stronger for the paid source model.

The degree-four homogeneous part of J is

    J_4 = -hE(wC-tr).                                      (4)

The quadratic D=wC-tr is irreducible: its symmetric matrix in w,C,t,r has rank four, whereas a product of two linear forms has rank at most two. Over any characteristic-zero field, the quadratic

    a*hE+b*D                                               (5)

has rank at least four whenever b is nonzero. The h,E block and the w,C,t,r block use disjoint variables, so their ranks add. Therefore the only nonzero decomposable quadratics in span(hE,D) are multiples of hE.

Suppose three multiplication gates suffice. Any gate whose output is affine can be absorbed into the free affine operations. With at most two genuine multiplication gates, a degree-four output has a quartic leader equal to a scalar times the square of the first gate's quadratic leader, incompatible with (4). Thus it remains to consider exactly three genuine gates g1,g2,g3, where g1 has degree two. Put Q1=(g1)_2; it is a product of two homogeneous linear forms. Every input to a later gate is an affine combination of the original variables and preceding gate outputs. The final output is an affine combination of those same values.

There are three exhaustive possibilities for the degree of g2:

* **Degree two.** An operand involving g1 has degree two; for its product still to have degree two the other operand would have to be constant. Such a gate contributes no new value beyond free affine operations and can be discarded. Thus an independent degree-two g2 has a decomposable leader Q2. To obtain a quartic at g3, both operands must have degree two. Their leaders lie in span(Q1,Q2), so J_4 is a product of two quadratics in that span. Unique factorization of (4) forces those two quadratics, in either order and up to nonzero scalars, to be hE and D. They are independent, hence span(Q1,Q2)=span(hE,D). But (5) says this two-dimensional space has only a one-dimensional subspace of decomposable quadratics. The decomposable Q1,Q2 cannot span it, a contradiction.

* **Degree three.** The cubic leader of g2 is Q1 times a linear form. The quartic at g3 can arise only from operand degrees 3+1 or 2+2. In the former case it is a product of four linear forms; in the latter it is a scalar multiple of Q1 squared, because any degree-two operand cannot involve g2. Neither possibility contains the irreducible quadratic factor D of (4). Earlier gate outputs have degree at most three, so they cannot change this quartic leader.

* **Degree four.** Its quartic leader is a nonzero scalar multiple of Q1 squared. If g3 has degree above four, its leading terms cannot cancel against earlier outputs, whose degrees are at most four; then it cannot be used in the target. If g3 has degree at most four and genuinely uses g2, its other operand must be constant, so it adds no value beyond free affine operations. Otherwise its quartic leader, if any, is again a scalar multiple of Q1 squared. Every degree-four final affine combination therefore has a quartic leader proportional to Q1 squared; if that leader cancels, its degree drops below four. Neither outcome is (4).

These cases also cover unused gates and cancellations: distinct degree levels cannot cancel a higher leader, and the degree-four/degree-four case explicitly allows cancellation of their common square leader. Thus three multiplication gates are impossible. At least four are necessary, independently of the number of additions.

Combining Sections 3 and 4 gives the exact bound **4M+5A=9**. The same bounds hold for any fixed nonzero scalar multiple of J.

## 5. Novelty and limits

The prior-art scan read the actual84 proof, local-producer scout, shared-fork scout, cross-block next note, transport quotient shear, and the first-norm polynomial-scaling bound; the indexed-source and outer-slack deletion notes were inspected to avoid retrying already refuted positive projections. Their relevant boundaries are:

* `complete84_local_producer_scout.md`, SHA-256 `7cfa58529ec02a6cf3df475e3d0feda6b4e5f4ad6b6c622e810907371b0aecad`, searches a single producer with at most two new operations.
* `complete84_shared_fork_scout.md`, SHA-256 `d2ba717ab229d830a4b73002edddd401c3f2046f46cdb050c6fcdceccaae091c`, searches two targets sharing at most three operations.
* `complete84_cross_block_next.md`, SHA-256 `f528326b033473e288c20da5ceb72bfd4cd94198ecfea11bf54f758a0ab3d5d5`, gives a multiplication-only monomial boundary and a tied outer-mask rewrite.
* `complete84_scaled_finalizer_boundary.md`, SHA-256 `492a07cd42913e88004ecaa0d65f4133c10d5caa6d529b27b5f8aa891748670e`, concerns a different six-port finalizer and arbitrary polynomial multipliers.
* `complete86_transport_quotient_shear.md`, SHA-256 `fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541`, is already present in the actual transport factor (1).

The present argument allows unrestricted circuit size, order, addition, subtraction, multiplication, reuse and scalar constants at its declared cut. It therefore extends beyond the earlier finite replacement grammars. Its target is the exact joint product, not arbitrary polynomial multiples of it. It does not price a complete source with additional donor registers, nor an evaluator that shares new gates with another factor. It also does not classify polynomials agreeing only on complete positive zeros. In particular, assigning both factors the value one after assuming a parent zero would delete precisely the conditions being evaluated and is not a justified replacement.

No new complete source, degree/witness tradeoff or universal bound is claimed. A useful next route must change this cut, use an extra shared value, or establish a genuinely new zero-set theorem. The source-count and independence assertions were checked by fresh read-only JSON/text inspection. No archived, supplied, frozen or predecessor program or source array was executed or imported; no numerical source evaluation was performed. This note is an elementary proof scout, with no executable packet or finite experiments substituted for the lower-bound argument.
