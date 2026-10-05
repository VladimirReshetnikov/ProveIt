# The complete84 main norm forces the sign of w

Allow the supplied coordinate `w` to be an arbitrary integer while retaining every other positive coordinate of the literal complete84 source. Every resulting integer zero still has **w>0**. This is a source-specific sign theorem, proved before native history decoding. It gives an exact positive chart `v=Kconstant+w` whose complete cost remains **84=47M+37A**. The dyadic chart `v=(Kconstant+w)/2` is also valid on the inherited compiler, but the direct fully paid realization costs **85=48M+37A**. Neither chart supplies an 83-operation construction or a global lower bound.

## 1. Literal interface and cancellation

The parent is `complete84_scaled_strong_output.json`, SHA256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`, with its full proof `complete84_scaled_strong_output.md`, SHA256 `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`. The six fixed numeral ports, ordinary positive input and other seventeen strictly positive witnesses are unchanged. In particular `MF` is the shifted source numeral, not the unshifted native mask.

Use literal source meanings

    q=Bm1*Jrep+1, X=w*q, Y=s*q^3,
    k=eta+zeta, cP=k*Y+eta, a=Y*(X+1),
    H=4*a+3, Delta=a^2+H=(a+1)*(a+3),
    gamma=rho+sigma, D=X+a*cP+gamma*H,
    Nm=D^2-Delta*cP^2.

Here `cP` is the Pell coordinate `R10a`; it is not the fixed shift used below. These definitions bind rows 2–3, 6–10, 15–29 of the saved source. Even when w is signed, q>=2, Y>=q^3>=8, cP>0 and gamma>0 follow directly from the retained positive coordinates and Bm1>=1. No norm equation or decoded history is used for these inequalities.

Let P be the product of the six factors other than the scaled strong factor, including Nm. The literal last rows and the paid coefficient definitions give, identically over the integers,

    F84=Delta*(P*Ns-1),
    Ns=f^2-Delta*i^2*cP^4.                         (1)

This is the already established all-ring identity F84=Delta*F85, now used on the stated partially signed domain. The expression P*Ns is a product of seven integer factors. No claim that the seven *scaled* complete84 factors are units is made.

## 2. Signed-w zero equivalence

**Theorem.** With all coordinates except w positive as above, an integer zero of F84 has w>0. Consequently extending only w from positive integers to all integers introduces no zero at all.

**Proof.** If w>=0 then a>=Y>=8, so Delta>0. If w<=-1, then X<=-q<=-2 and a=Y(X+1)<=-Y<=-8. Both a+1 and a+3 are negative, again giving Delta>0. Therefore Delta never vanishes on this partially signed domain. At any F84 zero, (1) implies P*Ns=1. Every integer factor, in particular Nm, must be either 1 or -1.

Suppose first that w<=-1. Then X<0, a<0 and H<0, so

    D=X+a*cP+gamma*H < a*cP < 0.

Thus D^2>a^2*cP^2 and

    Nm=D^2-(a^2+H)*cP^2 > -H*cP^2 > 1,

contradicting Nm=+/-1. The final strict bound already follows from a<=-8, H<=-29 and the positive integer cP.

If w=0 then X=0 and a=Y. Expanding the same literal main norm gives

    Nm=H*(2*a*cP*gamma+gamma^2*H-cP^2).

Here H=4Y+3>=35. Its nonzero integer multiple cannot be +/-1, and its zero multiple also cannot be +/-1. This is the remaining contradiction. Therefore w>0. The converse inclusion of the original positive zero set in the partially signed one is immediate. ∎

This proof is stronger than a statement only about canonical histories. Its algebra needs Bm1>=1 and the displayed other-coordinate positivity, not the special mask or transport numeral recipe. Universality and the dyadic divisibility used later remain inherited only on the authentic compiler slices. The old unrestricted-signed-domain warning in the parent remains correct: allowing other coordinates to be signed can produce Delta=0.

## 3. Translated positive charts and a fully charged tie

For any fixed nonnegative integer c0, substitute w=v-c0 into the complete polynomial and require v>0. At each child zero, the theorem forces the restored w positive. Conversely a parent positive zero gives v=w+c0>0. These maps are inverse on the entire positive zero sets, preserving the ordinary input and all other coordinates. This is an all-value polynomial substitution followed by a proved zero-set assertion; the two polynomials on identically named raw coordinates are not claimed equal.

Take c0=Kconstant=K>0. Exactly two parent rows directly consume w:

    wn2=w*q,
    kinner=Kconstant+w.

Replace the supplied w by `transport_coefficient` v, insert

    restored_w=transport_coefficient-Kconstant,
    wn2=restored_w*q,

at the old `wn2` location, remove the old `kinner` row, and replace its sole consumer by

    innerC=transport_coefficient*marked_rhs.

Every other row is literal. The added subtraction pays for restoring w; the removed addition used to build kinner. There is no new fixed port, comparison, inequality test or witness. The complete ledger is still 47M+37A=84, with eighteen positive witnesses. In particular, treating the positive transport coefficient as supplied does not make the subtraction needed by the main/first/input blocks disappear.

Static source reconstruction in the companion JSON records the full 84 rows, checks all operand bindings and topology, and confirms every row and all 25 supplied ports remain live. It does not evaluate any source array. Row induction proves that every retained old value is the parent value at w=v-K, with the removed kinner represented by v itself. Thus the complete child output is exactly F84(w=v-K), and Section 2 proves both directions of the positive-zero bijection. As an invertible affine change of one variable over the rationals, this also preserves the inherited exact total degree187 on every valid fixed slice.

More generally, w=v-rho and w=v-sigma are valid positive charts: their forward maps add an already positive coordinate. In the literal source each requires a paid restoration subtraction and does not remove the separate `gamma_sum=rho+sigma` or transport addition. This observation is not a lower bound for jointly redesigned consumers or different witness eliminations.

## 4. Dyadic absorption: valid, but the direct schedule adds a product

On every parent positive zero in the inherited valid compiler, native soundness yields

    q=2^t, t>=4, X=2^R, R>3q,
    w=2^(R-t).

These are the full-positive-zero conclusions inherited through the asymmetric-scale and later coordinate equivalences, not a fresh assumption of a selected completion. Since R-t>=1, w is even. The literal powers-of-five compiler has a unique lowest monomial V^(3*a_tiles) in K=DC+B*DR, with unit coefficient and all other terms at higher V-exponents, V=2^b. Hence v2(K)=3*a_tiles*b>=1: K is even as well. Only these two divisibility facts are used here.

The chart v=(K+w)/2 is therefore a positive integer at every parent zero. Restore it with the paid rows

    kinner=2*transport_coefficient,
    restored_w=kinner-Kconstant,
    wn2=restored_w*q,

and retain `innerC=kinner*marked_rhs`. Delete the old later kinner addition. All other source rows remain literal. Only the already available numeral2 is used. At every child positive zero the restored integer w is positive by Section 2. Therefore the child-to-parent map is valid without a divisibility hypothesis on arbitrary child tuples; conversely parent-to-child integrality follows from even K and w. The maps are mutually inverse on the full positive zero sets.

The old two rows `wn2=w*q`, `kinner=K+w` cost 1M+1A. Their replacements above cost 2M+1A. The complete ledger is **48M+37A=85**, still eighteen positive witnesses and exact degree187. The companion static reconstruction checks the full array, topology, all supplied ports and liveness. No external positive constraint, integer quotient operation or free coefficient multiplication is being hidden.

**Review remark 1 (the failed dyadic saving proposal).** The proposal “supply (K+w)/2 in place of w and remove the paid addition K+w” is valid as a coordinate idea but does not by itself save a gate. The old main and first-norm computations still need w. Restoring it costs the multiplication 2v and the subtraction 2v-K; relative to the original fork this adds one multiplication. This refutes that literal savings claim, not every possible dyadic chart or cross-block source redesign. The prior six-full-numeral odd-factor obstruction did not exclude division by powers of two, so it does not replace the present sign and integrality proofs.

## 5. Dependencies, evidence and remaining scope

In addition to the complete84 source and companion, the following inert dependencies were read:

| Document | SHA256 | Scope used |
|---|---|---|
| `complete75_asymmetric_scale_tradeoffs.md` | `3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2` | Lines1–108 and215–260; full-zero dyadic X/q recovery and inherited positive maps |
| `complete83_outer_family_sparse_two_primary.md` | `bda0275af08ceaf1637b6bfa3ba8a8347205f5a674783cec7105ca263bf3fb97` | Lines1–90; only literal compiler census and v2(K), not an 83 soundness claim |
| `complete84_fixed_numeral_padding_boundary.md` | `d3c0e7fad5c7bc35f9919744e03e9f0bc8182ddc9c8dce6de53fbfe603ccbe0f` | Full note; earlier restricted numeral barrier and recipe bindings |
| `complete86_transport_quotient_shear.md` | `fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541` | Full note; actual transported coordinate/charged formula |

All paths are in `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`. The complete84 JSON's inherited proof pins retain the full universality dependency chain. Those underlying native theorems are not reproved here. The novel sign theorem does not use that chain; only the dyadic chart's parent-to-child divisibility invokes it.

The companion JSON was generated by new metadata-only code: byte authentication, exact row replacements and a static dependency walk. There was no evaluation of the saved parent or either child array, no sampled purported compiler zero and no execution/import of supplied, archived, frozen or predecessor code. Repository and Git state were untouched. The proof establishes a new partially signed-domain theorem and two honest chart ledgers; the universal84 gate frontier remains unchanged.
