> Release binding: all new generated artifacts in this directory use the complete mixed-radix Wang943 tuple, B=2^(5^9), selected by COEFFICIENT_BINDING.json. Historical source tuples mentioned below document predecessors or valid alternatives, not the selected numerical instance. The sibling coefficients/COEFFICIENT_PROOF.md proves the full adapter and simultaneous canonical restrictions.

# Odd signed scale improves the low-degree integer frontier

## Explicit artifacts

The generator `build_low_degree.py` transforms the previously delivered exact low-degree residual systems, retaining their polynomial identities and replacing only the positivity representation of s. It emits:

- `integer51_degree4.json`: 51 unrestricted integers, 30 quadratic equations; sum of squares has exact degree4.
- `integer42_degree6.json`: 42 unrestricted integers, 21 equations of degree at most3; sum of squares has exact degree6.
- `integer36_degree8.json`: 36 unrestricted integers, 15 equations of degree at most4; sum of squares has exact degree8.

These improve the previous 54-variable quartic, 45-variable sextic and39-variable octic by three variables each. Each previous system had a retained independent s register AND three independent positivity parameters constrained by `s=Pos`. Replace the retained s by the affine odd parameter `s=2*s_odd+1` and delete that guard equation and its three parameters. Thus the saving really is three. In a fully substituted presentation the positive coordinate itself has already disappeared; replacing its three parameters by one odd parameter instead saves only two, as in the separate26-to24 construction.

The new artifacts select a coherent authentic T5263 coefficient quartet from package23. In sextic/octic port names Bm1 means beta and Kconstant means K; MF is always shifted MF_source. This is a whole-tuple substitution. The compiler adapter and signed-scale completeness hypotheses are documented by the pinned source, not inferred merely from the coefficient sizes.

## Parent identities and recovered domain

The literal parent files are in the previous deliverable at
`sources/previous-deliverable/domains/` (vendored here). They are derived from the original32-coordinate quartic system and the polynomial register eliminations in `15-release`. Their `DOMAIN_REDUCTION_PROOF.md` and vendored sources give the explicit algebraic restorations and source attribution. The present artifacts record parent hashes; the signed-scale theorem newly added here is from
`23-separating12/proofs/ODD_SCALE_27_PROOF.md` at
`VladimirReshetnikov/ProveIt@ae3007ca4467011e0e051c84acb4a1dd13971b0e`.

All old retained registers and quotients remain unrestricted integers. Six positive source ports are still guarded: J,F,alpha,z,eta,zeta. The multiplier is still odd, w is still a square, and s is now odd but may initially be negative. Every register elimination used by the sextic/octic parents is a polynomial identity valid on arbitrary integer assignments, not a positive-domain inference. The first-root shear in the sextic is an integer affine bijection, restoring `tau=tau_tail+E(c-eta)`.

For the sextic, its multiplier register is `I=i_normalized*(Dmain^2-1)`. The main norm gives `Dmain^2-1=Delta*c^2`, so the residuals imply the normalized strong equation `f^2-Delta*i_normalized^2*c^4=1`. For the octic, `I=i_ordinary*c^2`, and the strong equation is `I^2=Delta*(f^2-1)`. Their other restored residuals already use the merged auxiliary quotient T. Therefore, after restoring the old registers, these two systems satisfy exactly the normalized or ordinary signed equations in the package23 odd-scale theorem, with their index/transport factors equal to1. That theorem first excludes w=0 by the main norm modulo H, then excludes s<0. Its positive-domain compiler recovery proves soundness. No use of the old positive-s theorem is made before this new step.

The quartic uses exposed auxiliary quotients o,j rather than merged T. Its reverse proof needs one additional argument, given next.

## Quartic exposed quotients with negative s

The quartic's quadratic definitions recover

    q=beta J+1, Y=sq^3, X=wq, E=XY,
    a=(X+1)Y, k=eta+zeta, c=kY+eta,
    Delta=(a+2)^2-1, H=4a+3,
    Dmain=X+ac+gamma H,
    k=R+1+hE,
    tau^2=1+X Y^2(X Y^2+1)k^2.

Its shifted transport equation `(K+w)(q-F-alpha)=F+z(q-1)` gives C>0 directly because z,F,K+w are positive. The original quotient is z_old=z+1>0. It recovers the usual transport unit1.

Since s is odd, |Y|>=q^3; initially X>=0, |H|>1, and Delta>0. If X=0, the already integral main root Dmain=ac+gamma H would satisfy 1=0 modulo H. Thus X>0 before applying any rank theorem.

When s>0, the old quartic bootstrap applies unchanged. When s<0, put Z=-Y, B=(X+1)Z-2, c0=-c, P0=2XZ^2+1. First/main Pell classification and index congruence give, exactly as in Section2 of the package23 signed-scale proof,

    k=2 psi_P0(n), c0=psi_B(p), p>n>=24,
    c0>B Delta^2, c0>2p.

These deductions use the first norm, main norm, transport and index equations only. They do not require an already merged T and do not assume positive h. Thus the ordinary strong-rank theorem applies to |f|, |i|, |c| and parameter B in the negative case. In both signs it proves `f^2=1 mod c` (equivalently modulo |c|), as well as the standard rank bounds. This congruence is obtained from the rank theorem, not by cancellation modulo c.

The exposed equations are

    V=of-c=jc-R.

Hence `of+R=(j+1)c`, and

    o+Rf=f(of+R)-o(f^2-1)

is divisible by c. Since c!=0, the proof-only number

    T=(o+Rf)/c

is an integer of unrestricted sign. Its auxiliary expression is exactly

    c(Tf-1)-Rf^2=of-c=V.

Consequently the whole quartic solution now yields a solution of the ordinary signed-scale source system, including its merged integer T, and the package23 theorem applies. It excludes s<0 and recovers the genuine native blank tableau. This order avoids assuming the conclusion s>0 to reconstruct T.

## Completeness

From an accepting blank computation, the canonical source witness simultaneously has odd normalized/ordinary multiplier i, square w, and positive odd s, as proved in the package23 ODD_SCALE_27 completeness section. The old quartic/exposed-quotient and sextic/octic lift completeness constructions supply all remaining registers; the sextic first-root tail is allowed any integer, so its shear creates no sign restriction. The quartic shifted quotient z=z_old-1 is strictly positive because `(K+w)C-F>0` at the canonical witness (w>q>F and C>=1).

Choose Pos preimages for each of the six remaining positive ports and set s_odd=(s-1)/2. Every new residual vanishes. Conversely, soundness above proves any new zero has s>0, so even the old s guard could be reconstructed by Pos surjectivity if desired. The old and new systems are therefore equivalent in existence, with the authentic tuple and machine endpoint fixed.

## Exact degrees and evidence

The script checks literal substitution and one deleted guard per system; all residuals are expanded integer polynomials and all24-or-more variables are live. The exact sum-of-squares degree certificates are:

- Quartic: coefficient of tau^4 is1.
- Sextic: coefficient of Jrep^2 L^2 s_odd^2 is4*beta^2>0.
- Octic: coefficient of Jrep^6 s_odd^2 is4*beta^6>0.

Thus the degrees are not merely upper bounds or diagnostic specializations. The generated sparse expansions have342,467,845 symbolic terms respectively before fixed-coefficient substitution. The residual systems are often the clearer specification than these expansions.

The three-variable positivity theorem, signed-scale theorem, ordinary strong-rank theorem, polynomial register identities and authentic compiler correctness are ordinary proofs formalizable in ZFC. These checks do not add an end-to-end Lean/Rocq certificate and do not decide whether any zeros exist. Their absence is equivalent in ZFC to Con(ZFC), using the same finite syntactic refutation predicate as the calibrated K215 endpoint.
