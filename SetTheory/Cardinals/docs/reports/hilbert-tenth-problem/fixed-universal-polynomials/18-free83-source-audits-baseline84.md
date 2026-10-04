# Independent source audit: scaled 84-operation polynomial

**PASS. Update the reviewed minimum-operation baseline to 84 = 47M + 37A, with 18 strictly positive witnesses, ordinary positive input, and uniform exact degree 187.** This preserves every valid fixed-program hypothesis of the reviewed85 parent. It is a demonstrated construction, not an unrestricted circuit lower bound; the85/degree175 tradeoff remains available.

## Source and exact scope

Pinned commit: `20aafb9a524196eed950f47134f09bc1b4671bc3`.

- [Author proof](https://github.com/VladimirReshetnikov/ProveIt/blob/20aafb9a524196eed950f47134f09bc1b4671bc3/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.md)
- [Literal84 JSON source](https://github.com/VladimirReshetnikov/ProveIt/blob/20aafb9a524196eed950f47134f09bc1b4671bc3/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json)
- [Repository independent review](https://github.com/VladimirReshetnikov/ProveIt/blob/20aafb9a524196eed950f47134f09bc1b4671bc3/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete84_scaled_strong_output.md)

Five targeted files were fetched through the GitHub connector. Their exact UTF-8 bytes are verified against returned Git blob identities and recorded SHA256 values. The actual parent85 JSON equals the already audited local85 baseline byte for byte and authenticates to the84 receipt's parent pin. Seven available immediate parent proof/source/review files also authenticate. Two older reviewer Python files were not present locally and were not needed or fetched. The entire older dependency/compiler chain is not freshly re-audited here.

The author Python was read as text; its OLD/NEW/FINAL literal arrays were parsed inertly for cross-checking. No upstream Python was imported or executed, neither saved arithmetic schedule was evaluated, no upstream receipt was replayed, and no large positive Pell witness was materialized. The only executed code was this audit's independently written static graph inspection and explicit symbolic polynomial arithmetic.

## Complete source comparison

- Old: 85 live gates, 48 multiplications, 20 additions,17 subtractions
- New: 84 live gates, 47 multiplications, 20 additions,17 subtractions
- Every one of25 supplied ports is live:18 witnesses, ordinary input x, six fixed numerals
- Names/order of witnesses, input, free ports, and fixed numerals are identical
- Exactly79 complete row definitions are unchanged
- Removed names: ic2, ic22, strong_difference
- Added names: aux_coefficient_root, scaled_f_square
- Changed existing definitions: R16, norm_strong, polynomial
- All six factor-product gates are unchanged; the final subtraction costs one operation as before
- Producer core:41M+36A=77; finalizer:6M+1A=7

Complete old private consumers, including operand multiplicities, are ic2 -> both operands of ic22; ic22 -> strong_difference; strong_difference -> R16 and norm_strong. The strong factor is consumed only by seven_units in each source. The checker authenticates all row definitions, topological order, exact consumer occurrence sets, and output-rooted liveness.

The old paid main/strong shared producers remain. Consumers inside the replaced block naturally change: c2 loses ic2 while retaining Ac2; Ac2 gains aux_coefficient_root; L16 loses norm_strong while retaining auxiliary_R_f2 and gaining scaled_f_square. Thus the author's phrase that these producers retain "every original consumer" should be understood as retaining the necessary outside-block consumers, not a literally identical occurrence list. This wording imprecision has no mathematical or cost consequence; the exact consumer certificate is in CHECKS.json.

## Whole-ring identity and positive zeros

Write c=R10a, Delta=A, f²=L16, c²=c2, Delta*c²=Ac2. The old block computes

    t=i*c²; Q=Delta*t²; Kaux=Delta*Q; Ns=f²-Q.

The replacement computes

    S=i*Ac2; Kaux_new=S²; scaled=Delta*f²-Kaux_new.

Exact integer-coefficient expansion gives Kaux_new=Kaux and scaled=Delta*Ns. Therefore the auxiliary factor Kaux*(V²-y²)+y² is unchanged, along with the remaining five factors and the full quotient V. If P denotes the product of those six unchanged factors, the literal finalizers are

    F85=P*Ns-1,
    F84=P*(Delta*Ns)-Delta=Delta*F85.

The checker independently expands the coefficient identity, complete auxiliary norm, scaled strong factor, and whole output using explicit formulas. Static source/consumer checks connect these formulas to every saved row. No zero equation, sign, division, or domain assumption enters the all-ring identity.

On the positive supplied interface, Bm1=B-1>0 and J,w,s>0 give

    q=Bm1*J+1>0, X=wq>0, Y=sq³>0,
    a=XY+Y>0, Delta=(a+1)(a+3)>0.

Consequently F84=0 iff F85=0 over the integers, on the identical positive coordinate tuple. This transfers the prior full positive-zero/universality theorem with its exact inherited valid-program recipe, including shifted MF; arbitrary numeral assignments are not thereby compiler certificates. No new inverse map or rank/sign argument is required. At a new zero the scaled strong factor equals Delta, not necessarily1: recovering the parent zero precedes invoking its unit/sign conclusions. Signed tuples with Delta=0 are outside this cancellation argument.

## Uniform exact degree

The previously audited parent's degree is175. The retained source gives the leading form of a as w*s*Q^4, where Q=Bm1*J, so Delta has exact degree12 and leader w²*s²*Q^8. On each fixed-program slice the coefficient ring is an integral domain, hence deg(F84)=175+12=187.

The independent checker multiplies the reviewed175 leader by this Delta leader, obtaining all168 monomials of

    32 Q^111 h (rho+sigma) delta² i⁴ (eta+zeta)^13 w^18 s^31
       * Ttransport * auxiliary_quotient² * f²,

where Ttransport=w*(Q-F-Z-alpha-twice_cell_bits*x)-transport_quotient*Q. Every term has weighted degree187 when fixed numerals have degree0 and all witnesses/input have degree1. The coefficient of

    J^112*h*rho*delta²*i⁴*eta^13*w^18*s^31
       *transport_quotient*auxiliary_quotient²*f²

is -32*Bm1^112, nonzero uniformly because Bm1>0. The actual factor degrees are inherited22,18,32,60,7,2 and new46, summing to187. Subtracting degree12 Delta cannot cancel that leader. The author's naive upper bound197 is looser; it is not the exact degree.

## Reproduction and limitations

Run only this independent checker:

    python3 independent_static_audit.py
    python3 -O independent_static_audit.py

Normal and optimized executions passed and produced byte-identical results. Checks use explicit exceptions, not removable assertions. CHECKS.json records the complete consumer lists, authenticated bytes, ledger, and symbolic certificate; CHECKS.optimized.json is the independent optimized-mode replay of this new checker only. The prior175 theorem is inherited from the earlier audit rather than reproved from the entire compiler here. No repository modifications, public writes, uploads, or upstream checker reruns occurred.
