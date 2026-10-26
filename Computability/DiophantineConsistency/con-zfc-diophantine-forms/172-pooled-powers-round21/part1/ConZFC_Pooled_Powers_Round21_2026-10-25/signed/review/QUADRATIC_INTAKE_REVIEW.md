# Round21 independent quadratic-projection intake review

## Result

The supplied Quadratic Projection package passes its complete normal and deep-optimized verifier. Its principal endpoint is exactly 234 unrestricted integer coordinates, 171 quadratic residuals, degree four, 19,050 collected terms, coefficient height 4,480. The two factorial-free companions are exactly 235/170/18,550/H4,576 and 236/171/4,947/H16,866.

The new common-Hessian projection theorem and its affine-consequence variant are correct over unrestricted integers. The cofinal two-square beta-spacing theorem is also correct under the explicit hypothesis on the two-adic valuation of F. No new end-to-end formal proof or proof of consistency is established by these checks.

The actual pooled225 input contains FIVE useful common Hessian directions, not the six found in the quadratic package's different 240-variable parent. Exact finite composition gives:

| Endpoint | Variables | Residuals | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| incoming pooled225 | 225 | 162 | 4 | 7,867 | 128,446 |
| pooled220 | 220 | 157 | 4 | 7,790 | 142,238 |
| pooled219 | 219 | 156 | 4 | 22,754 | 247,319 |
| pooled218 | 218 | 155 | 4 | 22,799 | 13,607,184,407 |

The final row illustrates an extreme height tradeoff, not a small-coefficient improvement. The first affine relation alone gives 219/156/7,837/H13,607,065,661. No savings from different source variants have simply been added.

## Ordinary algebraic proof checked independently

Let Q_i be integer quadratics with Hessians H_i and linear vectors l_i. For an integer direction v with H_i v=0 for every i, exact expansion gives Q_i(y+s v)=Q_i(y)+s(l_i dot v). The mixed terms vanish by H_i v=0; twice the pure quadratic term is v^T H_i v=0, so that term vanishes as an integer too.

Assume v_p=1 and the selected slope a_r=l_r dot v is +/-1. Set y_p=0 and define R_i(y)=Q_i(y)-a_i a_r Q_r(y), i != r. A new root lifts integrally by s=-a_r Q_r(y), x=y+s v. An old root projects by y=x-x_p v. The selected equation forces s=x_p, so both maps are inverse. Every new residual remains quadratic. No rational division or positivity assumption is hidden in this operation.

For a constant integer row combination L=sum lambda_i Q_i whose primitive affine normalization has unit coefficient at p, solve x_p=S in integer affine terms. Substitution keeps all rows quadratic. Omit any row r with lambda_r != 0. The affine consequence becomes identically zero; if the retained rows vanish then lambda_r Q_r=0, hence Q_r=0 in the integers. The inverse inserts S. A unit combination coefficient is unnecessary; the variable coefficient after primitive normalization must be a unit.

Each elementary integer row operation Q_i <- Q_i+k Q_j, i != j, is inverted by subtracting k Q_j in reverse order. Thus all recorded row operations preserve the common zero set. A sum of integer squares is zero exactly when every row is zero.

## Literal pooled composition

At the original pooled225 coordinate indices, the five directions are:

1. v25=-1, v27=1, v28=2;
2. v31=-1, v32=1, v33=2;
3. v44=-1, v45=1;
4. v61=-1, v62=1, v63=2;
5. v64=-1, v66=1.

All unlisted entries are zero. The direction slope vectors have unit entries. The emitted order is different because the constructor minimizes a finite score: deleted original register names are mul.188, add.277, mul.303, add.112, add.71. The exact renumbered directions and inverse polynomials are in pooled220/projection_certificate.json.

After those five projections, two independent affine consequences remain:

    -R6+R19 = 4+12*x9+16*x10+4*x20-x21+x34,

    R81 = x95-9*x9-9*x10-4*x20-2*x23-2*x27-2*x29
          -2*x31-2*x33-4*x36-2*x37-2*x40-2*x43-4*x62-2*x63.

The chosen pooled219 solves the second relation for x95. The pooled218 stage then solves the first for x34. The final constant quadratic row-combination kernel is zero. The common Hessian kernel at pooled220 is zero, certified by full rank modulo the explicitly checked prime 1,000,003. These facts concern only the named moves on the literal presentations; they are not global optimality certificates.

## Cofinal beta-spacing proof and compatibility

Write t!=2^a m, m odd, and suppose 2^a divides F^2. For each odd prime p, the squares and minus one minus the squares each occupy (p+1)/2 residues, so there are A,B with A^2+B^2=-1 mod p. At least one coordinate is nonzero mod p; changing it by delta*p^j lifts the solution to p^(j+1), since its derivative is a unit. CRT yields m dividing 1+A^2+B^2. Then

    y_k = F^2*(1+(A+k*m)^2+B^2)

is an unbounded family of multiples of t!, each expressible as F^2+u^2+v^2. If F is even all y_k are even. This proves the needed unbounded theorem, not merely the 195 finite sample checks.

For the factorial-free branch F=[2(t+1)]^t the two-adic hypothesis is automatic. The new beta row gives y>=F^2>F+1 after the already independent positive-base power certificate authenticates F. The signed bootstrap first derives representative nonnegativity from q+1>=2, B!=0 from its index row, then x>=0 from |BH|>=2. The last endpoint excludes x=0; the first then excludes a negative u0 and gives x>=F+1. Finally ut>=1 gives x>=2+(t+1)y. Thus the parent's strict binomial and digit estimates remain available without assuming a sign before decoding it.

For completeness the finite pending-state path is built before y is chosen; choose a cofinal y exceeding it. The beta moduli are pairwise coprime by the usual index-difference argument, and all are odd. Their odd product allows a sufficiently large even CRT code x. The parent's odd B and precision modulus leave the representative parity choices available, so q=(BH)^x is an odd square. This is an existential source replacement, not a pointwise extension to the old condition y/F being an odd square.

**Composition restriction:** pooled225 already uses the sharper semantic choice y=V-1, removing the y coordinate. Its front uses F=t!, not the factorial-free F=[2(t+1)]^t. Therefore this two-square beta mutation is not an additional pooled225 saving and was not composed with it. Only the universal exact algebraic projection theorem was transported.

## Source and verification evidence

The package's exact source ZIP pins and selected members pass independently checked byte comparisons. Shared-factorial source ZIP SHA-256 is 8c126ebd9982e547f16e86cf65b57dbc85bf72e98032237ab0c324afc1694ef2; factorial-free source ZIP is 38dfec4f7db8ba4af921fe101714da6a569a3afce1d916325eb550160372c913. The extracted copies under source_replay are the only source copies executed; original intake files were not modified.

Receipts VERIFY_NORMAL.json and VERIFY_DEEP_OPTIMIZED.json include every input-stage identity, projection, inverse row replay, coefficient of each expanded polynomial, rank facts, printed principal equation, corruption controls, and all source archive hashes. PYTHONOPTIMIZE=1 was set for the optimized command, so nested Python children inherit optimization.

The shared-factorial parent was run normally with --rebuild and optimized: SHARED_PARENT_NORMAL.json authenticates 35 byte-identical regenerated JSON files across seven build stages, as well as all retained parent checks. FACTORIAL_FREE_NORMAL.json authenticates 18 byte-identical regenerated JSON files, 12 public alias files, the independent source/power-interface checks and all parent checks. Their optimized counterparts are separate receipts.

For the new pooled composition the independent checker imports no producer implementation. It uses the direct directional row-combination formula instead of the producer's shear/substitution. The pooled220 audit checks all five steps, 60 numerical lift controls, eight deliberately corrupted certificates and every expanded coefficient. Both affine audits check exact row combinations, unit restoration, omitted-row recovery, quadratic substitution, all coefficients and five corruption classes. Normal and optimized receipts are present for each selected endpoint.

## Portable algebraic module

portable/ contains the unchanged projection, affine and independent-checker modules; their upstream notices and mathematical proofs; the exact pooled225 input; and the three selected projected endpoints with certificates and full expansions. Run `python3 -B replay.py` or `PYTHONOPTIMIZE=1 python3 -B -O replay.py` there. This replays every construction and the independent exact audits without search or external packages. Its whitelist is in PORTABLE_WHITELIST.json.

The portable module proves only the new algebraic equivalence. A complete consistency-equation release must retain the pooled225 ordinary arithmetic/logical proof closure separately. The named C222/ZF and ZF/ZFC calibration interfaces remain inherited; these finite checks neither compile that full transitive proof-assistant closure nor prove Con(ZFC).
