# Joint auxiliary producers under separated monomial scaling

The actual auxiliary quotient, coefficient and scaled strong factor admit a **10=7M+3A** joint producer schedule. In the separated arithmetic model defined below, **every nonnegative monomial rescaling of the strong factor still requires at least7 nonconstant multiplications and3 additions/subtractions**. Thus this family cannot reduce the complete84 circuit. The exponent quantifier is unbounded; the conclusion is not a finite search over a few multipliers.

The restriction is substantial: monomials are produced by multiplication, then combined additively. General circuits that multiply sums, changed coordinates, extra paid ports, or a simultaneous change of the auxiliary coefficient are outside the theorem. No lower bound for the whole universal polynomial is claimed.

The [fresh helper](complete84_auxiliary_monomial_scaling.py) and [receipt](complete84_auxiliary_monomial_scaling.json) retain the full parent and a complete84 attaining source. All predecessors are read as inert bytes/JSON; none is imported or executed.

## Actual ten-row interface

In [complete84](complete84_scaled_strong_output.md), use

    c=R10a, Delta=A, R=r_lhs, T=auxiliary_quotient,
    V=c(Tf-1)-R f²,
    Q=(i*Ac2)²=Delta² i² c⁴,
    S=Delta f²-Q,
    c²=c2, Ac2=Delta*c².

The paid cut inputs are Delta,c,i,f,T,R,c²,Delta*c². The last two are dependent monomials, not unrelated supplied variables. In particular **f² is not a paid input to this joint cut**: its producer is included. The six core variables are independent for the local arithmetic theorem; only the two displayed monomial dependencies are admitted.

The ten actual rows are `L16`, `auxiliary_Tf`, `auxiliary_Tf_minus_one`, `auxiliary_c_Tf`, `auxiliary_R_f2`, `aux_u_rhs`, `aux_coefficient_root`, `R16`, `scaled_f_square`, `norm_strong`. Their only outputs consumed outside the cut are V,Q,S. In particular f² feeds only the quotient and strong producers inside this cut. The helper authenticates all ten definitions, both paid-square/coefficient definitions, and the complete consumer map.

An attaining separated schedule is

    f2=f*f; Tf=T*f; cTf=c*Tf; Rf2=R*f2;
    coefficient_root=i*Ac2; Q=coefficient_root²;
    scaled_f2=Delta*f2;
    V=(cTf-c)-Rf2; S=scaled_f2-Q.

It has seven multiplications and three subtractions. The helper replaces the parent's two-row `Tf-1; c*(Tf-1)` ordering by `cTf; cTf-c`. Exact coefficient expansion proves the same intermediate, and exact expression interning through all later rows proves the same seven factors and complete polynomial. The entire attaining source has **84=47M+37A** live operations, unchanged18 positive witnesses and inherited exact degree187. No arithmetic result is inferred merely from a finite evaluation.

## Model and theorem

Let M be any nonzero scalar times a monomial with nonnegative exponents in Delta,c,i,f,T,R. The required outputs are

    V=cTf-c-Rf², Q=Delta² i² c⁴,
    S_M=M*(Delta f²-Q).

In the first phase, the circuit computes monomials using products of supplied monomials and earlier monomials. In the second phase, it uses additions/subtractions and scalar linear operations to form the displayed outputs. No product of two nonconstant expressions is allowed after a nonmonomial sum has been formed. Equivalently, the nonmonomial output stage is a linear circuit on the computed monomials. The full circuit may share any first-phase intermediate among its outputs.

For the lower bound, arbitrary scalar multiples may be provided for free. This relaxes the paid model and cannot make the lower bound stronger than justified. Constant-scaling products therefore need not be counted; the seven required products are nonconstant ones. The three addition bound counts binary additions/subtractions, even with arbitrary scalar linear weights available.

First-phase outputs can be assumed irredundant. A useful computed monomial must divide some required output monomial: multiplication only adds nonnegative exponents, and the second phase cannot create a missing monomial. A scalar multiple of an already available monomial adds no new capability in the relaxed model.

## Seven multiplications for every multiplier

The three unchanged required monomials are

    A1=cTf, A2=Rf², A3=Delta² i² c⁴.

None is supplied and none is a product of two supplied monomials, so each needs at least two multiplications. For A3, two copies of i would use both factors and leave the Delta/c exponents missing; the paid Ac2 cannot supply the missing i exponent alone. The same direct check for A1 and A2 includes both extra paid ports c² and Delta*c². The helper checks all pairs of the exact finite input set.

No useful new product can be shared between these three cones. Their pairwise greatest common monomial divisors are respectively

    gcd(A1,A2)=f, gcd(A1,A3)=c, gcd(A2,A3)=1.

Every divisor of these gcds is already supplied. Any intermediate shared by two cones would divide that pair's gcd and would thus be redundant in the relaxed model. Consequently at least **six distinct multiplication gates** are needed to supply A1,A2,A3 together.

Now consider the strong output's first monomial

    M*Delta*f².

It contains both Delta and f for every nonnegative exponent vector of M. No supplied monomial contains both. Nor does any of A1,A2,A3 contain both: A1,A2 have no Delta, and A3 has no f. Thus this required monomial needs a multiplication outside all three preceding cones. There are at least **seven nonconstant multiplications**, independently of the degree or support of M. Requiring the other strong monomial M*Q can only add obligations; it cannot remove this bound.

The argument is a divisor/support proof for all exponents. The receipt checks its fixed monomial premises, not a finite list as a substitute for the quantifier. It also preserves the actual dependency Ac2=Delta*c² throughout.

## Three additions for every multiplier

V has three distinct monomials. Both monomials of S_M have positive Delta exponent, whereas none of V's monomials has a Delta factor. The two supports are therefore disjoint, for every allowed M; the two strong monomials are themselves distinct.

Suppose the linear output stage used at most two additions. V needs both, since one addition of monomials has at most two terms. The two-term S_M must then be available at the first addition, up to scalar multiple, because it cannot be a monomial input. The second addition either ignores that first sum, leaving at most two terms, or combines it with one monomial. One further monomial cannot cancel both distinct strong-support terms and simultaneously produce V's three disjoint terms. The same argument covers reuse of the first sum twice, which cannot produce a new support. This contradiction proves the **three-addition** bound, irrespective of the number of first-phase products.

The attaining M=1 schedule shows the joint bound10 is sharp in this model. Attainment at10 is not claimed for nonconstant M.

## Full-output scaling and limits

Writing the product of the other six actual factors as P_other, the complete parent is

    F84=P_other*S-Delta.

Replacing S by M*S and the final subtraction by M*Delta computes M*F84. The other producer rows and finalizer multiplications are retained in this family; computing the new final offset is an additional obligation. The local lower bound already prevents a saving even if that offset were provided free. The helper emits the complete attaining M=1 source, not a claimed finite catalogue of all scaled sources.

For a positive-domain scaling, restrict M to the unconditionally positive source quantities Delta,c,i,f,T. They are positive before any equation is imposed, so M*F84=0 and F84=0 have the same positive tuples. The broader formal exponent theorem also permits R, but **no positive-zero equivalence is claimed when R is a multiplier**: its off-zero nonvanishing is not assumed. All fixed-program hypotheses and ordinary-input semantics remain those of the parent.

This complements rather than adds together the older isolated bounds. The quotient scout treated f² as already paid; the auxiliary/strong five-gate cut treated Q and Delta*f² as independent paid outputs. Here those producers are charged jointly, and the rescaling exponent is unrestricted, but the evaluation model is narrower than arbitrary arithmetic. An improvement along this cut must exploit a sum inside a later nonconstant product, change the retained coefficient/output interface, use additional paid algebraic relations, or leave the monomial-scaling family. The proof does not prohibit those routes.

## Pins and replay

| Parent file | SHA-256 |
|---|---|
| `complete84_scaled_strong_output.py` | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| `complete84_scaled_strong_output.json` | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| `complete84_scaled_strong_output.md` | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |

The receipt includes both full84 arrays, all cut consumers, exact monomial identities and sixteen supplementary complete signed evaluations. The latter are polynomial checks, not constructed positive compiler zeros. Duplicate JSON keys and nonfinite values are rejected, receipt comparison is recursively type-exact, and checks remain active under optimized Python.

```sh
aux_wip=/absolute/path/to/native-stream-queue
python3 "$aux_wip/complete84_auxiliary_monomial_scaling.py" \
  --root "$aux_wip" --expect "$aux_wip/complete84_auxiliary_monomial_scaling.json"
python3 -O "$aux_wip/complete84_auxiliary_monomial_scaling.py" \
  --root "$aux_wip" --expect "$aux_wip/complete84_auxiliary_monomial_scaling.json"
```

Fresh normal and optimized exact replays from `/` pass. No predecessor executable or frozen repository file is changed.
