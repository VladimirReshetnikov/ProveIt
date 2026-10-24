# Independent review: the first-root carrier in fifteen integers

## Verdict

PASS as an ordinary, unbounded arithmetic reduction to the exact pinned normalized seventeen-integer source. The new carrier, all-sign recovery, and both integer witness maps are valid. The complete literal polynomial has fifteen unrestricted integer inputs, exact degree 56, and 110 live binary operations: 63 multiplications, 24 additions, and 23 subtractions. No claim of a new kernel-checked compiler theorem, encoded internal-ZFC derivation, consistency proof, or global minimum follows from this review.

The reviewed candidate is `/lowdegree/equation.json` relative to this packet. Its exact SHA-256 and finite verification results are in CHECK.json. The independent checker imports neither the candidate builder nor its arithmetic library. It separately checks thirty named expressions by exact symbolic cuts, graph closure/liveness, every highest homogeneous component, authentic complete coefficient bytes, and nine deliberately corrupted live operations. It passes in ordinary and optimized Python. This finite checking complements the unbounded reasoning below; it is not its substitute.

## 1. The carrier works over all integers

Write ell=XY^2 and L=ell*k. The first row is exactly

    Z^2 + 2ULZ - U^2(ell*k^2+1).

The affine restrictions and authentic beta prove, without using a row or guard, that q is even, q=2 modulo 3, and q is nonzero. Also H=4a+3 is odd and nonzero, while H=3 modulo q. Thus gcd(H,2q^2)=1 and U=(2q^2)H is nonzero, even when q or H is negative.

At a zero, t=Z/U is a rational root of the monic integer polynomial

    t^2 + 2Lt - (ell*k^2+1).

Monicity is essential and is present. Therefore t is integral. Setting tau=t+L gives tau^2=1+ell(ell+1)k^2. Since U divides Z, its literal definition gives simultaneously

    2q^2 divides v-q^2, and H divides Klo.

Both cancellations use the already-proved coprimality, not any presumed Pell orientation. In particular v=0 would imply 2q^2 divides q^2, impossible. Thus the first row itself excludes v=0 before any large-scale estimate. It recovers v=q^2(2v0+1) and Y=(2v0+1)q^3 with integral v0.

Finally Klo=2K-HXc for K=X(X+2ac)-1. Odd H makes H|Klo equivalent to H|K. No factor q is cancelled modulo H after the fact, and no nonmonic rational-root claim is used.

## 2. The changed guard supplies the needed hypotheses, not more

Pos is positive for every integer triple, so the guard forces

    k^2 [q^2-(cone_A F-q)^2-(cone_B C-q)^2] > 4q^2 eta^2.

Consequently k is nonzero, the two squared errors sum to less than q^2, and |eta/k|<1/2. The two cone constants are at least 8. Thus F/q and C/q are positive and their sum is less than one, making F,C,alpha=q-F-C share q's strict sign. Together with the recovered nonzero Y, this gives c nonzero,

    |k|(|Y|-1)<|c|<|k|(|Y|+1),
    sign(c)=sign(kY).

It would be invalid to assert eta(k-eta)>0 at this point. The candidate does not do so. The exact centered-budget source explicitly proves that the weaker interval and sign facts above suffice for the signed rank/bootstrap, and later restores eta>0 by its uniform nearest-half-binomial argument. Its completeness uses the same authenticated source34 family with a strict budget margin. There is no mixing with the compact44 tuple or transfer of a positive-domain theorem to unrestricted integers.

## 3. Omitted main-root recovery does not assume the projection

With B0=|a+2| and I0=|2r+1| |c|^2, the cubic scale and budget imply B0>=3, I0>=|c|>0, Delta=B0^2-1, and f0=|f|>2I0. The normalized strong row gives Q=(Delta I0)^2=S^2 with S>=2. The centered auxiliary row is exactly

    S^2 V^2-(S^2-1)(V+y)^2=1.

Both V and V+y are nonzero: either being zero is immediately incompatible with this equation and S>=2. Classify S|V| and |V+y| by the Pell sequence of parameter S. Its index ell must be odd because chi_S(even) is ±1 modulo S. The odd quotient identity evaluated at S^2=1-B0^2 modulo f0 and V=-c modulo f0 gives psi_B0(ell)=±|c| modulo f0.

The strong pair is (chi_B0(m0),psi_B0(m0)). The addition identities give folding modulo f0 to ±psi_B0(p), with 0<=p<=m0. The strict bound I0+|c|<=2I0<f0 excludes all nonzero multiples of f0 and forces psi_B0(p)=|c|. Thus p>=1 and the missing main norm has an integer root. Neither gamma nor H|K nor an orientation was used in this classification.

## 4. Signed rank and whole-product projection

The first Pell classification holds for negative X as well: use the positive consecutive-product parameter -XY^2-1 if X<0. The recovered cubic scale and native packing bounds give |XY|>3R+1 and |2XY^2+1|>|a+2|. Together with the main ordinate from Section 3 they give p>n0 and the signed first-index congruence. Its negative branch implies n0>R; the positive branch implies n0>=(R+1)/2. Pell growth yields the stated large-ordinate bounds before strong-rank use.

The normalized rank lemma requires only |c|^2|I0; it gives |c||m0 and m0>2p without assuming an odd auxiliary root. The packed V satisfies V=-c modulo f0 and V=-R modulo |c|. The inherited signed auxiliary step-down therefore gives p=R. This excludes the negative first-index branch and gives 2n0=R+1, so R=2s+1 with s>=24.

The ratio estimate uses only the already-established magnitude interval, not eta positivity:

    |Y|>(|X|-3)^s/2-1.

For x=|X|>=64 this entails |H|>x(x-3)^s. The elementary bound

    (x-3)^s >= (x/2)61^(s-1) > x*2^(5s-6) >= x*2^(4s+4)

holds for s>=24, and proves |H|>2^(2R+2)x^2. The signed Pell identities modulo H show, for x0=sign(c)X,

    2^R K = (x0-2^R)(2^R x0+1) modulo H.

Hence H divides this whole product. Each factor has absolute value less than 2^(R+1)x, so the product has magnitude less than |H| and must vanish. Its second factor is odd, hence nonzero. Therefore x0=2^R. With d=sign(c)chi_(a+2)(R), the congruence H|(d-X-ac) follows. This proves integral gamma and recovers the exact original main row. It does not make a primewise branch selection modulo composite H.

## 5. Both source maps are genuinely integral

New to source17: J3=2j, F_source=F, alpha_source=q-F-C, z_source=z, v_scale=(v-q^2)/(2q^2), tau_source=Z/U, and gamma_source=(d-X-ac)/H, with all other retained coordinates unchanged. Every quotient has already been proved integral. Source tau is centered, so it is Z/U, not Z/U+L. Source y is also centered and is unchanged. The eliminated transport row is an identity because F=(K0+W)C-z(q-1). The eliminated mask expression is preserved because

    (q-1)(q-F)+(q-F-C)=q(q-F)-C.

Thus all six exact source residuals vanish. The source's complete late-orientation and compiler theorem is used only after this literal source zero exists.

Source17 to new: its proved power theorem forces X=2^R. Since q|X and |q|>=16, q is even. Beta is odd, so 3J3+1=(q-1)/beta is odd, proving J3 even and j=J3/2 integral. Put v=q^2(2v_scale+1), C=q-F-alpha and retain the transport z. This recovers exactly the source F and R. The source main row gives H|K through

    (X+ac)^2-(1+Delta c^2)=K-Hc^2,

hence H|Klo. Set n=tau_source-Klo/H-v_scale. Then Z/U=tau_source, proving the new first row; all other rows agree. This reverse map works for every old zero, so canonical completeness alone is not being used to disguise a nonintegral inverse.

## 6. Exact degree and literal cost

Independent degree propagation gives row degrees 28,14,18,16. The carrier has unique highest contribution -U0^2 k0 L0. Its square is the only degree-56 term of the final sum of squares. With q0=6 beta j, W0=12w, X0=q0W0, Y0=q0v, selecting the h term in k0 gives

    [j^30 w^10 v^12 h^4] P = 2^62 3^40 beta^30 > 0.

The exponents sum to 56. This proves exact degree for the authentic coefficients, rather than merely a syntactic upper bound or generic-coefficient result. All fifteen variable leaves, all six coefficient leaves, and all 110 binary gates are live. Scalar multiplication and squaring are charged in that count.

## 7. Evidence and limits

The six complete coefficient payloads were decompressed and compared byte-for-byte with the inherited centered17 payloads, in addition to their binding hashes and literal beta/cone recipes. The same normalized17 JSON and all cited ordinary proofs were read. The independent checker rejects mutations to Klo, the carrier, strong and auxiliary rows, the guard, the final sum, F, R, and Z. It also checks signed and zero-v CRT examples, but those examples are diagnostics only.

The ordinary proof above closes the new arithmetic reduction. It inherits, rather than newly formalizes, Pell classification/rank/step-down and the exact source34 native/compiler/refutation calibration. In particular, this audit does not turn finite checking into a proof of Con(ZFC) or into a claim that the end-to-end compiler theorem has been proof-assistant verified.
