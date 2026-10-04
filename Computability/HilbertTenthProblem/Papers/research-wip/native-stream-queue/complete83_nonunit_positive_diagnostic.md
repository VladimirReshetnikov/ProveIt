# A materialized nonunit zero of the complete 83-gate polynomial on diagnostic numerals

The [checker](complete83_nonunit_positive_diagnostic.py) and [receipt](complete83_nonunit_positive_diagnostic.json) give an exact, fully materialized zero of the frozen [free-coefficient 83-gate source](complete83_free_coefficient_scout.md). All 18 supplied witnesses, the ordinary input, and all six fixed numeral values are positive integers. In the source's factor order the values are

    (first, main, input, auxiliary, index, transport, scaled strong)
       = (1, 1, 1, 1, 1, -675, -1),
    Delta = 675,
    product - Delta = 0.

**The fixed numerals are deliberately not a valid compiler recipe.** This is a complete source zero on a diagnostic coefficient slice, not a false accepted input on any valid compiled program, not a counterexample to the 84- or 85-operation theorem, and not an 83-operation universal bound. It rules out inferring the intended individual factor values merely from positivity of the supplied coordinates and fixed numerals together with the complete product equation. Compiler-specific hypotheses remain available and necessary for any stronger conclusion.

## 1. Exact assignment

Use Pell polynomials defined by

    chi_A(j) + psi_A(j) sqrt(A²-1) = (A + sqrt(A²-1))^j.

The mathematical Pell parameter A is 26; the source register named `A` instead contains its discriminant Delta=675. Set

    (D,c)       = (chi_26(1351), psi_26(1351)),
    (tau,k/2)   = (chi_257(855), psi_257(855)),
    (mu,kappa)  = (chi_26(17), psi_26(17)),
    gamma      = (D-24c-2)/99,
    rho        = (mu-24kappa+4)/99.

The checker constructs these three pairs by fresh integer binary powering, verifies their Pell norms, and checks every division exactly. It also checks the strict inequalities

    8k < c < 9k,       gamma > rho > 0.

The six fixed numeral ports and ordinary input are

| Port | Value |
|---|---:|
| `Bm1` | 1 |
| `Kconstant` | 1 |
| `twice_cell_bits` | 2 |
| `inner_bits` | 15 |
| `MC` | 2694 |
| `MF` | 2 |
| `x` | 1 |

The 18 supplied witnesses are

| Port | Value |
|---|---|
| `Jrep`, `F`, `alpha`, `f`, `auxiliary_quotient`, `s`, `w`, `Z` | 1 each |
| `transport_quotient` | 670 |
| `aux_coefficient_root` | 26 |
| `tau_root` | tau |
| `eta` | c-8k |
| `zeta` | 9k-c |
| `h` | (k-2702)/16 |
| `y_aux` | 2703 |
| `delta` | (kappa-17)/675 = 4210554269281735945232016 |
| `rho` | 56864361637967446931750178 |
| `sigma` | gamma-rho |

All entries are positive integers. The largest supplied value has 7,699 bits, so this example is actually materialized, not an invocation of an unmaterialized large-witness existence theorem. The receipt records all 25 supplied values and all 83 computed register values as signed hexadecimal strings.

## 2. Actual source factors

The literal source computes q=2, X=wq=2, Y=sq³=8, E=XY=16, a=Y(X+1)=24, and H=4a+3=99. Thus its first Pell parameter is 2XY²+1=257. The choices of tau and k give its first factor 1. The definitions of eta, zeta, rho and sigma give its exact main ports c and D, so the main factor is also 1.

The computed input ports are

    W = q-F-2Z-alpha-2x = -4,
    C = W+Z = -3,
    u = 2x+15 = 17,
    kappa = u+delta*675,
    mu = W+24kappa+99rho.

They agree with the displayed input Pell pair, hence the input factor is 1. Positivity is asserted for supplied coordinates; computed W and C are negative in this diagnostic.

The actual packing and index rows give

    gap = q²-qF-Z = 1,
    R = gap*(q²-1) + (MC+q*MF)*Jrep = 2701,
    k-hE-R = 1.

With S=`aux_coefficient_root`=26, f=T=1, the actual auxiliary argument is

    V = c*(Tf-1)-Rf² = -2701.

Consequently

    scaled strong = 675*1²-26² = -1,
    auxiliary = 26²*2701² - (26²-1)*2703² = 1.

The latter identity is the index-3 Pell identity: 2701=4*26²-3 and 2703=4*26²-1. Finally the actual sheared transport factor is

    (Kconstant+w)*C + q-F - transport_quotient*(q-1)
      = 2*(-3)+1-670 = -675.

These are checks of the source's existing rows and final product, with no inserted equations or changed factor definitions. The checker evaluates the complete 83=46M+37A schedule and verifies that every paid gate and every supplied port is live.

## 3. What the diagnostic does and does not settle

For any integer zero of this complete polynomial with Delta>0, the seven integer factors multiply to positive Delta. Hence every factor is nonzero, each divides Delta, its absolute value is at most Delta, and an even number of factors are negative. None of these elementary facts forces all factors to be positive or forces six factors to be 1 and the scaled strong factor to be Delta. The displayed complete assignment realizes a negative transport divisor and a negative scaled strong factor.

The compiler exclusions are concrete. Here B=`Bm1`+1=2 and q=2 violate the compiler's B,q≥16 pretyping range. MC=2694 is outside 0<MC<B-1. The unshifted mask is MF0=MF-(B-1)=1, outside its strict range and not 4 modulo 8. The supplied width `inner_bits`=15 exceeds the cell width d=`twice_cell_bits`/2=1. Splitting Kconstant=DC+B*DR gives DR=0 rather than a positive program numeral. Also q=B corresponds to N=1, inconsistent with the required positive-input bound 2x<N at x=1. Thus neither the program recipe nor the intended mask/input interface is being certified.

This diagnostic does not establish a nonunit branch on a valid compiler slice, does not decide the 83-gate candidate's ordinary-input language, and does not change the established 84-operation bound. It is distinct from the earlier free-coefficient extension theorem: that theorem retains the intended factor values on already accepted compiler inputs, whereas this diagnostic exhibits different factor values using inadmissible fixed numerals.

## 4. Reproduction and scope of the checker

The helper authenticates the frozen free-coefficient source, receipt and proof note; reads the receipt as inert JSON; and imports or executes no predecessor code. It uses only the standard library. It reconstructs the complete assignment, exact Pell identities and divisions, source closure, liveness, paid counts, all register values and the full finalizer. Its explicit checks remain active under optimized Python. The saved receipt is compared with exact JSON types, including the full source and complete assignment.

For installed frozen parents in the WIP directory:

```sh
python3 complete83_nonunit_positive_diagnostic.py --root /absolute/path/to/native-stream-queue --expect complete83_nonunit_positive_diagnostic.json
python3 -O complete83_nonunit_positive_diagnostic.py --root /absolute/path/to/native-stream-queue --expect complete83_nonunit_positive_diagnostic.json
```

Fresh normal and optimized exact receipt replays from `/` pass. This is a bounded pinned-data diagnostic CLI, not a maintained compiler API, a search census, or a proof of compiler admissibility.
