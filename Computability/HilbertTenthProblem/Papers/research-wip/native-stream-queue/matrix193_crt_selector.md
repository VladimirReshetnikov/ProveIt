# Exact integer CRT lookup lowers the matrix193 countdown to 154 operations

The complete [source](matrix193_crt_selector.py) and [receipt](matrix193_crt_selector.json) replace the six polynomial interpolants in the [1179-operation countdown](matrix193_unimodular_selector.md) by six fixed CRT tables and seven integer interval certificates. The resulting synchronized predicate costs **128=61M+67A**, and the complete countdown costs **154=73M+81A**, at exact degrees **8 and 10**. The countdown saves **1025 operations** against its immediate parent.

This is an exact **signed-integer** local relation, with **35 auxiliary integer witnesses per step**. It is globally nonnegative over the reals, but its real zeros do not characterize the matrix transitions. The receipt includes an explicit rational false transition. A second complete schedule costs **146/172**, uses 41 auxiliary integer witnesses, and has lower exact degrees **4/6**.

For fixed duration h>=1, the 154-operation source gives **155h+7 operations and 40h signed witnesses**. A paid shared-offset conversion gives **195h+7 operations and 40h+1 positive witnesses**, with degree at most 10. Complete positive sources for h=1,2 are saved at **202/397 operations** and **41/81 positive witnesses**. These are local and fixed-duration results; unbounded duration still requires a fixed-arity history representation. The universal 84-operation bound is unchanged.

## 1. Actual data and the fixed-numeral recipe

The helper authenticates the immediate parent trio as inert bytes:

| File | SHA256 |
| --- | --- |
| `matrix193_unimodular_selector.py` | `34c98040cf2d20d88fbfdfe7e71ae88d6904547a5ab8102c0805c71d6bccc456` |
| `matrix193_unimodular_selector.json` | `c03bc63e10398bb53e19fd1ad6f755fa132164379dce10c523de3ea0dd598e1c` |
| `matrix193_unimodular_selector.md` | `87ee28420daa8d722b495137a9e76b316a74e95c64c94f656f592849f06640b2` |

It also pins the [Gamma1 recoding](matrix193_gamma1_recode.md), [context absorption](matrix193_context_absorption.md) and [synchronized-row proof](matrix193_synchronized_rows.md) for the uniform-context statement below. No predecessor Python is imported or executed. The selected fixture's 96 paired matrices, tile identifiers, order, initializer and endpoint are unchanged.

Write `v_(c,i)` for the entries in the six retained columns `K0,K1,K2,G0,G1,G2`, at indices i=0,...,95 in the saved order. Put

```
T = 1 + max_(c,i) |v_(c,i)|,
L = 96!,
m_i = 1+(i+1)L,
M = product_(i=0)^95 m_i.
```

For the actual table T has 103 bits and L has 499 bits; the helper checks `2T<min m_i`. The moduli are pairwise coprime: a common divisor of m_i and m_j is coprime to L and divides `(j-i)L`, hence divides j-i. Since every nonzero difference has absolute value at most 95 and divides L, that divisor is 1.

For each retained column compile the least nonnegative integer

```
C_c = sum_i (v_(c,i)+T) * (M/m_i) * inverse(M/m_i mod m_i)  mod M.       (1)
```

All operations in (1) are fixed-data compilation. They specify actual integers, not a variable division or an unpriced variable lookup. Each residue `v_(c,i)+T` is strictly between 0 and m_i. The helper independently checks all 4,560 pairwise gcds and all 576 residue matches. M has 48,333 bits; the six C_c have at most 48,333 bits. The receipt stores each fixed numeral exactly in hexadecimal, with its effective recipe and fingerprint. Every variable use is paid under the same arbitrary fixed-integer leaf convention as the parent. No bit-cost improvement theorem is claimed.

The repeated K matrices and the parent's irregular G-entry labels are not needed. The selector is the ordinary integer index i, preserving exactly the same paired choices.

## 2. An integer interval certificate and the complete selector

For integers v,h with h>=0,

```
0<=v<=h  iff  there exist integers s0,s1,s2,s3
                  v(h-v)=s0^2+s1^2+s2^2+s3^2.          (2)
```

The forward implication uses Lagrange's four-square theorem, including the trivial zero case. The reverse implication uses nonnegativity of a sum of squares: the product is negative outside the interval. This classical existence theorem is an explicit dependency; its formal statement is [Mathlib's Nat.sum_four_squares](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/SumFourSquares.html#Nat.sum_four_squares), and the theorem is also stated in [NIST DLMF 27.13(iii)](https://dlmf.nist.gov/27.13#iii). This packet does not claim that the full source has been formalized there.

Supply an integer selector z and seven independent groups of four signed square witnesses. Let S_z denote the four-square sum for z, and S_c the sum for column c. The shared producers are

```
h=L(z+1), m=h+1.                                       (3)
```

First require

```
z(95-z)-S_z=0.                                        (4)
```

By (2), z is an integer in 0,...,95. Consequently m=m_z>0 and h=m_z-1>0. This establishes the positive interval endpoint before any residue interval is used.

For each column supply an integer quotient q_c and **compute**, rather than supply,

```
v_c=C_c-m*q_c,
a_c=v_c-T.                                            (5)
```

Require the six residuals

```
v_c(h-v_c)-S_c=0.                                     (6)
```

Equation (2) forces `0<=v_c<m_z`. The quotient is integral, so (5) makes v_c the unique least nonnegative residue of C_c modulo m_z. Equation (1) therefore proves

```
v_c=v_(c,z)+T, a_c=v_(c,z).                            (7)
```

For each chosen z the remainders and quotients are unique. The four-square witnesses need not be unique, and transition endpoints need not identify a unique tile. The same z is used for every column, so synchronization is preserved.

Conversely, every chosen table index has the integer quotients in (5), the indicated remainders, and integer four-square extensions for (4) and (6). No bound or sign assumption is imposed on a supplied quotient; its value is fixed on tile zeros.

Use the parent's determinant-one, nonzero-pivot row equations, now without a common interpolation scale. For a row `(u,v)` and its proposed successor `(p,q)`, the three recovered matrix entries a,b,c enforce

```
p-a*u-c*v=0,
a*q-b*p-v=0.                                         (8)
```

Every actual matrix `[[a,b],[c,d]]` satisfies `ad-bc=1` and `a!=0`. The second expression equals `a*(q-b*u-d*v)-b*(p-a*u-c*v)`. Thus (8) is equivalent to the full row action, over the integers and also over the reals once the matrix has been recovered. The helper checks these hypotheses on all 192 actual matrices. It uses (8) for K and G at the same z.

The complete synchronized polynomial U is the sum of the squares of (4), the six residuals (6), and the four residuals (8): **eleven residuals** in total. It is nonnegative on every real tuple. Over integer state and auxiliary coordinates, an existential zero is exactly one of the original 96 matched transitions.

The integer hypothesis is essential. At z=0, take every v_c=T and `q_c=(C_c-T)/(L+1)`, allowing rational quotients, and choose integer square decompositions of `T(L-T)`. Then all six a_c are zero. The state rows `(1,0),(1,0)` can falsely map to `(0,0),(0,0)` under (8). No invertible actual matrix does that. All other auxiliaries can be integral, and the receipt verifies this complete rational zero in both schedules and both countdown wrappers. Real nonnegativity supports conjunction; it does not restore real transition exactness.

## 3. Full paid source and a lower-degree alternative

The computed-remainder schedule has the following ledger. Every row, supplied port and fixed-numeral binding is live.

| Complete synchronized stage | M | A | Total |
| --- | ---: | ---: | ---: |
| Shared h,m | 1 | 2 | 3 |
| Selector interval residual, including four squares | 5 | 5 | 10 |
| Six computed remainders, interval residuals and shifted entries | 36 | 42 | 78 |
| Four row-action residuals | 8 | 8 | 16 |
| Eleven residual squares and their complete sum | 11 | 10 | 21 |
| **Synchronized** | **61** | **67** | **128** |
| Entire inherited countdown wrapper | 12 | 14 | 26 |
| **Countdown** | **73** | **81** | **154** |

The 35 auxiliary coordinates are z, six integer quotients and 28 square witnesses. The seven four-square sums cost 28M+21A, all included. The fixed table is not charged as a free query.

The second saved mode supplies six additional integers v_c and adds the six residuals `C_c-m*q_c-v_c`. Each still uses the same interval product and row equations. Its six extra residual producers and finalizer squares/joins add **18=6M+12A**, giving **146=67M+79A** synchronized and **172=79M+93A** countdown, with 41 auxiliaries. Both directions are exact: on a supplied-mode zero, the six equations force the computed values; every computed zero extends uniquely in these six coordinates. In fact substituting (5) makes the entire supplied polynomial identical to the computed polynomial, for all scalar values, not merely on zeros. The helper checks both whole-polynomial pullbacks.

The four saved local arrays contain exactly **600 paid rows**. A fresh sparse polynomial interpreter compares every complete output and residual with separately written formulas in independent state, auxiliary and fixed-numeral ports: **34,881 output coefficient entries** in total. This includes the full finalizers and both countdown wrappers. No column count is substituted for a whole-source ledger.

In supplied mode all residuals have degree at most 2, so U has degree at most 4. Setting every state and square witness to zero, every q_c and v_c to zero, and z=t leaves `(t(95-t))^2+sum_c C_c^2`; its leading coefficient is 1. Thus the exact degree is **4**.

In computed mode v_c has degree 2 and the range residual can have degree 4, so U has degree at most 8. On the same zero-state line with z=t and additionally `q_K0=t`, its unique degree-eight contribution has coefficient `L^4>0`. Thus the exact degree is **8**. The helper checks these actual-DAG specialization polynomials with the actual fixed integers. No zero-only matrix identity is used to reduce formal degree.

The untouched countdown wrapper specializes, with n=t and next_n=0, to `(t-1)^2*(U_line+t^2)`. Its exact degrees are consequently **6** in supplied mode and **10** in computed mode. Neither exact local degree is silently asserted after all possible fixed initial substitutions.

## 4. Ordinary input, fixed duration and paid positive witnesses

The complete wrapper is retained from the parent, with only its tile-polynomial wire changed:

```
U_count = E_load * (U+n^2+(next_n)^2).                 (9)
```

Here E_load is the five-square polynomial enforcing

```
next_X=X,
next_Y=Y * [[52891,-29036],[94920,-52109]],
next_n=n-1.
```

All 26 wrapper instructions are retained literally up to register names. Both factors of (9) are nonnegative on real tuples. Over integers a zero therefore means LOAD, or an actual matched TILE with both counters zero. On a LOAD all CRT auxiliaries may be arbitrary integers; no selector or remainder condition is accidentally required.

The initializer remains

```
X=(35426321,-19628667), Y=(1,0), n=ordinary_x,
```

with **zero input gates**. The exact endpoint polynomial is

```
(X0-Y0)^2+(X1-Y1)^2+n^2,
```

with its unchanged **7=3M+4A** source. The signed-counter argument forces every finite accepting trajectory at natural x to have shape `LOAD^x TILE*`: exactly x decrements are required to reach zero, and a load after the first tile would make return to zero impossible. The faithful matrix/word and ordinary-input transfer remain the explicitly inherited group and context theorems. The fixture is not asserted to be a universal compiled program.

For a fixed duration h>=1, supply five next-state coordinates and 35 CRT auxiliaries per step and sum all h nonnegative countdown polynomials with the endpoint. The h joining additions are paid. This gives

```
155h+7 operations, 40h signed witnesses, degree <=10.  (10)
```

For positive witnesses, supply one shared positive integer s and 40h positive integers p_j, and compute each distinct signed history/auxiliary coordinate once as `p_j-s`. Every finite signed list has such an extension by choosing s larger than the negative of its least entry and larger than zero. Conversely each positive tuple gives a signed integer list. These **40h paid subtractions** give

```
195h+7 operations, 40h+1 positive witnesses,
degree <=10.                                         (11)
```

The ordinary input is unchanged; it is neither shifted nor counted as a witness. State coordinates are shared across adjacent steps, so they are not reconstructed twice. The helper saves the entire positive h=1 and h=2 arrays, at 202 and 397 operations, with 41 and 81 positive witnesses; it checks closure, liveness, the degree upper bound and six full composition evaluations each. Their positive fibers exist exactly when the corresponding fixed-duration integer histories do. It makes no claim that either short duration accepts the concrete fixture.

The supplied-v alternative similarly gives `173h+7`, 46h signed witnesses and degree at most 6; its corresponding shared-offset construction has upper bound `219h+7`, 46h+1 positive witnesses. The synchronized supplied-target version of the computed mode has `129h+5`, 39h signed witnesses and degree at most 8.

These are finite-duration compiler bounds, including the endpoint and positive conversion. Quantifying h does not create one polynomial with fixed arity. Unbounded packing, common duration and the resulting fixed-variable arithmetic remain unpaid.

## 5. Uniformity over inherited fixed contexts

The CRT construction applies to any fixed table of 96 integral determinant-one paired matrices with nonzero first entries. For larger entries choose

```
T=1+max |retained entry|,
L=96! * ceil((2T+1)/96!).                              (12)
```

This is a positive multiple of 96!, exceeds 2T, and retains the same coprimality proof. Formula (1) then compiles the six fixed integers. No variable gate count changes; the literal schedules charge every fixed-coefficient use regardless of its value. The fixture uses L=96! because its entries already satisfy the bound.

The inherited context family meets the nonzero-pivot premise uniformly. The Gamma1 recoding places H' inside `Gamma_1(5)`, where each upper-left entry is 1 modulo 5. Context absorption keeps every H_i,G_i,C in H', and synchronized preprocessing uses `K_i=C^(-1)H_i C`. Thus all K_i and G_i remain in that group and their first entries cannot vanish. This proves a uniform **154-operation integer local countdown upper bound** for the inherited fixed-context numeral recipe, and the fixed-duration bounds above. Only the one selected numeric table is emitted here; no arbitrary-program compiler was run. The faithful encoding and simulation results are inherited, not re-proved by the CRT arithmetic.

## 6. Fresh verification and replay

The helper checks all six source/proof dependency pins, the parent JSON self-source identity, all 192 determinants/pivots, every fixed CRT residue and all whole source identities described above. It also checks 768 row actions at all 96 nodes, including rational row inputs after actual integer coefficients are recovered, and 48 complete signed/rational off-zero source comparisons against direct formulas.

Two actual selector nodes have saved exact integer four-square decompositions of their six range products, of sizes up to 608 bits. They produce eight complete integer tile zeros across the four local arrays and eight nonzero wrong-successor tests. Four integer LOAD fixtures verify that the auxiliary conditions need not hold on that branch. Four complete rational false-transition zeros establish the real-domain limitation. Every saved square decomposition is checked by integer multiplication and addition. A probable-prime routine was used only during scratch candidate search for these finite decompositions; no primality assumption enters the helper or the proofs.

The receipt records 34,881 full formal coefficient entries, the two all-value pullbacks, exact local degree lines, all 600 local rows and 599 positive-history rows. Checks remain active under `python3 -O`. The bounded CLI rejects duplicate keys, noninteger numeric syntax and nonfinite JSON values, compares receipts recursively with exact types, and creates outputs exclusively.

With this trio and its six pinned dependencies installed, from any working directory:

```sh
crt_wip=/absolute/path/to/native-stream-queue
python3 "$crt_wip/matrix193_crt_selector.py" --root "$crt_wip" --expect "$crt_wip/matrix193_crt_selector.json"
python3 -O "$crt_wip/matrix193_crt_selector.py" --root "$crt_wip" --expect "$crt_wip/matrix193_crt_selector.json"
```

Fresh writer and normal and optimized exact replays from `/` all passed on the frozen source and receipt. No predecessor or archived software is executed by this packet.
