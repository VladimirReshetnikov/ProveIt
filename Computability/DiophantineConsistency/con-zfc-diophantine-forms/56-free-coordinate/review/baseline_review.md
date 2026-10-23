# Independent current-frontier audit

Snapshot inspected: `4b4349064a750ba6347293b55874a7f92abdd0db` of VladimirReshetnikov/ProveIt, 23 October 2026. Read-only repository inspection; extracted text references live under scratch `audit_work/`. No repository mutation.

## Critical baseline corrections

The eight incoming ZIPs already improve substantially on the placed wave-5/6 catalog. Comparing a new result only with package 40 or 45 would miss the actual current frontier.

| Scope | Best reviewed incoming point(s) | Source |
|---|---|---|
| Fifteen positive, fewest operations | 66 operations, exact degree 157 | `con_zfc_sparse_arithmetic_2026-10-23.zip`, `short/generated/p66_degree157.json` |
| Fifteen positive, short tradeoffs | 68/113, 72/80, 74/68 (operations/degree) | Same archive, short subtree |
| Fifteen positive, degree 44 | 75 operations (signed recovery), 76 operations (direct six-comparison equivalence) | `ConZFC_Sparse_Support_2026-10-23.zip`, minima subtree |
| Fourteen positive | 79 operations, degree 56 | `ConZFC_Support_Sensitive_2026-10-23.zip`, fourteen subtree |
| Eleven positive | 113 operations, degree 954; two-equation maximum degree 952 / 108 operations | `con-zfc-sparse-pell-124c07c0b7.zip`, positive subtree |
| Twelve positive | 108 operations, degree 897; three-equation maximum degree 888 / 102 operations | Same sparse-pell archive |
| Nine positive, smallest reviewed degree | 7,344,328 / 738 operations | `ZFC_Diophantine_Selective_Quadratic_2026-10-23.zip` |
| Nine positive, cheaper tradeoffs | 10,127,484 / 655; 10,486,092 / 603; 15,502,748 / 548 | `con-zfc-sparse-pell-124c07c0b7.zip` |
| Ten unrestricted, smallest reviewed degree | 21,111,400 / 659 operations | `ZFC_Diophantine_Selective_Quadratic_2026-10-23.zip` |
| Ten unrestricted, cheaper tradeoffs | 34,378,296 / 637; 50,822,936 / 582 | `con-zfc-sparse-pell-124c07c0b7.zip` |
| Thirteen unrestricted, without Sun 2026 | 57,866,184 / 759 | `ZFC_Diophantine_Selective_Quadratic_2026-10-23.zip` |
| Smallest reviewed native tuple | B=2^429959, 215,492 raw payload bytes | `con-zfc-selective-2026-10-23.zip`, coefficient_adapter subtree; not substituted into that archive's principal equations |

These values are source claims read in primary repository artifacts, not an assertion that every supplied driver was rerun in this audit. The old catalog's statement that 67 operations is unbeaten is superseded by the incoming squared-modulus construction.

## Independent check of the squared-modulus argument

The incoming `SQUARED_MODULUS_PROOF.md` has a valid ordinary mathematical argument. Write A=a+2, Delta=A^2-1, c=psi_A(R), R=3 mod 4. If S^2=Delta(f^2-1) and c divides S, then the odd Chebyshev polynomial Q_r with chi_t(2r+1)=t Q_r(t^2) obeys

Q_r(0)=(-1)^r(2r+1), Q_r(1-A^2)=(-1)^r psi_A(2r+1).

With r=(R-1)/2 odd, V=Q_r(S^2) gives V=-c mod f^2 and V=-R mod c. For the canonical normalized witnesses supplied by completeness, f^2=1 mod c and gcd(c,f)=1 hold as well. These two properties must not be inferred from the ordinary strong equation alone. Consequently V+c+Rf^2 is divisible by c f^2 and is positive. The fresh quotient T=(V+c+Rf^2)/(c f^2) satisfies V=f^2(cT-R)-c. Soundness is the exact substitution T_old=fT. Completeness chooses fresh auxiliary Pell witnesses; it does NOT assert that every old T is divisible by f. This saves one gate because f^2 is already available.

The same congruence construction extends to the ordinary strong form S=i c^2 by starting from a canonical normalized completeness witness and setting i_ordinary=Delta i_normalized. This retains f^2=1 mod c and gcd(c,f)=1, in addition to S^2=Delta(f^2-1) and c|S. The ordinary strong equation alone is insufficient for that inference. The combination with the incoming degree-44 minimum argument has now been materialized as a 74-operation, exact-degree-46 circuit; a further unit-product regrouping gives 73 operations at exact degree 54. Their complete mathematical review is in `../short/INDEPENDENT_REVIEW.md`, and their literal circuits and exact symbolic audits are included in this package. Neither point displaces the incoming 66-operation record or the degree-44 alternative.

## Formal and semantic boundaries

The active research has closed executable nine-natural and nine-positive definitions. `ExplicitZFC.noNaturalZero_iff_conZFC` and `NativeZFC.noNaturalZero_iff_conZFC` are external Lean theorems about the actual syntactic predicate `not BProv ZFCax_s [] Form.fBot`; the coefficient recipe is executable and closed, with no compiler premise. Numerical expanded payload is not materialized.

The short materialized P67/P69/P73/P75/P76 and incoming short refinements retain ordinary native-compiler, Pell, and calibrated K215 semantic proofs. Their local algebraic identities and some parents are Lean checked, but they do not inherit the generic executable compiler's end-to-end kernel theorem merely because they express the same goal.

`OBJECT_ZFC.md` explicitly leaves an exported proof term in the object-language ZFC calculus open. This does not refute the ordinary mathematical assertion of formalizability in ZFC. It does mean one must distinguish an ordinary proof formalizable in ZFC, an external Lean theorem about syntactic consistency, and an actual `BProv ... (iff ...)` derivation. The sources do so.

The nine-positive, nine-natural, and ten-unrestricted domains cannot be interchanged silently. Constants must be entire coherent native tuples; MF_source already contains the source mask shift. The incoming shortest circuit uses package36's tuple; most sparse-source archives use package31's tuple; sparse-pell uses package39/44's tuple. A circuit identity may hold symbolically while semantic validity still requires the full correct tuple.

## Further avenues and nonresults

- The incoming 75/76-operation degree44 minimum-norm proof uses ordinary strong and y=V+e, not a coordinatewise substitution into the normalized P76. Its lower degree cannot be claimed from the current Lean P76 theorem alone.
- A weighted minimum-norm combiner for the 31-positive quartic could save a small number of additions, but would need weights large enough to force all other residuals to vanish before using norm nonvanishing. A naive unweighted subtraction can introduce spurious zeros.
- Replacing separate eta,zeta positivity guards in integer quartics by eta*zeta>0 may reduce auxiliary variables, but the both-negative branch is not excluded by the presently inspected signed-domain theorem. No improvement is established along this avenue.
- No evidence here proves global optimality, fewer than nine natural unknowns, or fewer than ten unrestricted integer unknowns.
