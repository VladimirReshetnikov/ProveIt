# Six-unit bound scout: separate integer and positive families

The actual complete retained-a,c source admits one more unit port at a cost of one addition. Fully paid regrouping gives two all-integer candidates and two further positive-domain candidates:

| Candidate | Group equations | Comparison gates | Complete SOS | Exact degree | Witnesses |
|---|---|---:|---:|---:|---:|
| Integer `108_degree30` | `N0=1, Nk*Ni=1, Nb*Nm*Na=1` |79=43M+36A|108=53M+55A|30|24|
| Integer `110_degree24` | `N0=1, Nk*Nm=1, Nb*Ni=1, Na=1` |78=42M+36A|110=53M+57A|24|24|
| Positive `106_degree42_positive` | `Nk*Nm*Na=1, Nb*N0*Ni=1` |80=44M+36A|106=53M+53A|42|24|
| Positive `108_degree28_positive` | `Nb*N0=1, Nm*Na=1, Nk*Ni=1` |79=43M+36A|108=53M+55A|28|24|

The 110/24 source also belongs to the positive family. Every schedule retains the full ordinary input, all 24 supplied witnesses, the same compiled numeral ports, every other required equation, and the parent's unbounded duration. The all-integer candidates preserve the entire integer zero set on the same coordinates. The additional positive candidates have the same positive zero set, with the inherited admissible program slice required for universal semantics; no signed-zero equivalence is asserted for those additional forms.

This is a bounded source/proof scout, not a maintained public compiler. It changes neither the frozen parents nor the separate 74-operation comparison minimum. The two finite families below are restrictions defined by their sign proofs, not a claim about all equivalent regroupings or globally optimal circuits.

## Authenticated starting source

The [scout source](complete_bound_unit_scout.py) pins the frozen [index-unit packet](complete109_index_unit_tradeoffs107.md) and selects its actual canonical asymmetric `sos` parent: 113 operations, 13 comparisons, 24 positive witnesses, exact degree24. The direct pins are:

- Python `d255896294684f8d6411d992f5f0ba60a7f4051aa841d7e325f5347d64c23600`.
- JSON `3d8d8d473cc866ebd585ac5605648839cfe014e98b5be2a10938cc0dfcfe12b3`.
- Markdown `928f760d73a7da081eace63cfcb144f41cd4271fcd92fbc3860d482738b16b9b`.

It also enforces every source, receipt, and proof pin declared by that authenticated parent. The selected full parent is copied into the new [receipt](complete_bound_unit_scout.json). The source imports the pinned index-unit helper only for its strict provenance reader and canonical-parent selection; it does not call that helper's rewrite, full verifier, grouping census, or polynomial expansion. The new literal rewrites, sparse coefficients, degree proofs, finalizers, counts, and censuses are computed locally.

The first five units are those already proved in the parent:

```
N0 = g^2 + L*(2g-k),             L=X*Y^2*k,
Nm = d_main^2 - Delta*c^2,
Ni = mu^2 - Delta*kappa^2,
Na = (i*c^2)^2*((j*c-r)^2-y_aux^2)+y_aux^2,
Nk = (k-r)-h*E,
Delta = a^2+4a+3,
q = Bm1*Jrep+1, X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta.
```

The actual supplied a,c, ordinary strong equation, ordinary input norm, and all input congruences stay in the source. There is no new coordinate map, new witness, weak-norm replacement, or hidden external horizon.

## Exact bound port and complete paid cost

Comparison0 of the literal 113 parent is `raw_bound=q`, with paid rows

```
raw_bound = Z+W+alpha+twice_cell_bits*x,
repunit = Bm1*Jrep,
q = repunit+1.
```

Add exactly one row

```
bound_unit = raw_bound-repunit.
```

Write this port as Nb. Then `Nb-1=raw_bound-q` identically over every commutative ring. This preserves the entire old comparison residual, not just its zeros. The q row and all q consumers remain paid. There is no privacy claim for q and no attempted deletion of this shared register.

The previously paid five-unit core is 75=40M+35A. The new six-unit core is therefore 76=40M+36A. Six old comparison residuals become unit-minus-one residuals; the first has the opposite sign, removed by squaring. The other **seven** original comparison residuals remain literally unchanged.

For g groups, multiplication of the six factors takes `6-g` extra multiplications. There are `7+g` comparison residuals. Each pays a subtraction and a square, and their SOS pays `6+g` final additions. Thus

```
comparison gates = 82-g,
full M = 40+(6-g)+(7+g) = 53,
full A = 36+2*(7+g)-1 = 49+2g,
complete operations = 102+2g.
```

The receipt constructs every counted schedule, checks all source operands and all gates/coordinates for liveness, and independently regenerates the complete SOS. No factor product, ordinary row, or finalizer operation is omitted.

## Two distinct sign theorems

For every integer a, Delta is 0 or3 modulo4. Hence neither Nm nor Ni can equal -1. Writing `t=i*c^2`, Na is congruent modulo4 to either `y_aux^2` or `(j*c-r)^2`, so Na cannot equal -1 either. These are all-integer identities and use no other equation.

An integer product equal to1 has only factors +1 or -1. Therefore any group containing at most one of the three unprotected factors N0,Nk,Nb forces every factor to be+1. Each partition obeying this restriction has precisely the parent's entire integer zero set: its product equations recover all six old unit equations, and the converse is immediate. The full SOS has seven unchanged ordinary squares.

For the second family only, N0 is additionally protected on the **positive** source domain. This uses the already pinned sign proof in [complete113_asymmetric_retained109.md](complete113_asymmetric_retained109.md), Section2, SHA256 `cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0`.

On a positive tuple, b=Bm1>0 and Jrep>0 give q>=2. Consequently `V=X*Y^2=w*s^2*q^7>1` before any equation or native theorem. With `T=V*k+g`, the first norm is `T^2-V(V+1)k^2`. Suppose this is -1 and choose a solution with minimal positive integer k. Put

```
D=V(V+1), A=2V+1,
k'=A*k-2T,
T'=A*T-2D*k.
```

Because `A^2-4D=1`, the norm is unchanged. From `T^2=D*k^2-1` one has `0<k'`; and `T^2-V^2*k^2=V*k^2-1>0` gives `k'<k`. Finally `T'^2=D*k'^2-1>0`, so replacing T' by its nonzero absolute value gives a smaller solution, a contradiction. The checker verifies the norm-preservation identity by exact independent coefficient expansion. This proof does not rely on any other certificate residual, computation typing, or the parent's universal theorem.

N0,Nm,Ni,Na are therefore protected on positive tuples. Any partition keeping Nk and Nb in different groups forces all six factors to1 and preserves the full positive zero set. The new source does **not** infer protection of N0 over all signed integers: it records an actual signed source tuple with N0=-1. This tuple is a sign-boundary check, not a claimed complete false accepting zero. No signed-zero claim for the additional family is made.

## Finite censuses and exact degrees

Using order `(N0,Nm,Ni,Na,Nk,Nb)`, the actual factor degrees are

```
(12,4,7,10,7,1).
```

Let b=Bm1, J=Jrep, and define

```
Ftop = b^7*w*s^2*(eta+zeta)*J^7*(2g-eta-zeta),
Dtop = b*w*J+4*ga*a,
Mtop = Dtop^2+2*a*c*Dtop,
Itop = -4*delta^2*a^5,
Atop = i^2*j^2*c^6,
Ktop = -h*w*s*b^4*J^4,
Btop = Z+W+alpha+twice_cell_bits*x-b*J.
```

Independent multivariate expansion of the actual emitted core proves these six highest homogeneous forms. Every one is nonzero on every admissible fixed b>0 slice. In particular, Btop has alpha coefficient1; other fixed numeral choices cannot cancel it. The remaining seven residuals have degree at most6.

For every partition in either family, the exact full degree is twice the largest sum of its factor degrees. Products of nonzero highest forms have degree equal to the sum. The complete highest form is a real sum of squares of the maximal group leaders and cannot cancel, including ties. This proves the degree formula uniformly in the fixed program, rather than inferring it from finite specializations.

All 203 set partitions of six distinct labels are enumerated. The all-integer restriction retains **77**:

| Groups | 3 | 4 | 5 | 6 |
|---:|---:|---:|---:|---:|
| Integer-certified partitions |27|37|12|1|

Its exact operation/degree frontier is **108/30, 110/24**. A short check of the first minimum is informative: if three groups all had weight at most14, the weight12 factor would have to stand alone, since every permitted protected addition has weight at least4. The remaining weight29 cannot fit in two weight14 groups. Weight15 is attained by the displayed108 candidate. Four groups attain the unavoidable weight12 lower bound.

The positive-only sign restriction retains **151** partitions, equivalently all partitions with Nk and Nb separated (`Bell(6)-Bell(5)=203-52`):

| Groups | 2 | 3 | 4 | 5 | 6 |
|---:|---:|---:|---:|---:|---:|
| Positive-certified partitions |16|65|55|14|1|

Its exact frontier is **106/42, 108/28, 110/24**. These minima are also sharp within the stated weight family: the total weight41 forces a group of weight at least21 with two groups and at least14 with three; the weight12 factor is unavoidable for four or more. The displayed partitions attain those bounds. The 77 integer-certified partitions are a subset of these151, so the two census passes do not represent228 distinct partitions.

The four emitted candidate leaders are:

```
108/30: (Btop*Mtop*Atop)^2,
110/24: Ftop^2,
106/42: (Ktop*Mtop*Atop)^2,
108/28: (Mtop*Atop)^2+(Ktop*Itop)^2.
```

The last has two distinct maximal residuals, both degree14; there is no unsupported unique-leader assertion. The receipt verifies these exact highest polynomials against the complete candidate sources.

The catalogue comparison is pinned to the preceding index-unit receipt only; parallel or later censuses are not silently included. Relative to that catalogue, these candidates improve its high-cost degree frontier. They do not reduce its minimum complete universal operation count86. A maintained successor should compare against the then-current complete frontier separately.

## Full off-zero identities and replay

For any displayed partition G, the complete correction from the selected 113 parent is exactly

```
F_G-F_parent = sum_(groups C in G) (product_(i in C) N_i-1)^2
              -sum_(six units i) (N_i-1)^2.
```

All seven ordinary residual squares cancel identically. This identity is valid on signed and rational tuples for both families, even where a positive-family zero-equivalence theorem is unavailable. Every old comparison has an explicit current group/retained map. The receipt expands each full correction in six formal unit variables, then verifies its substitution into actual whole sources and all13 parent residuals.

The executable pins its complete starting source, constructs all 77 integer schedules and all151 positive schedules during the census, records deterministic source digests, and saves four complete source/finalizer packets. It checks192 complete corrections (96 signed integer and32 rational),2,496 individual residual values, all live ledgers and exact multivariate leaders,128 modulo4 cases,16,000 integer-factor regressions and12,800 positive-protected factor regressions. The proofs above establish the general claims; the finite checks supplement them. No astronomical accepting witness or unchanged historical suite is replayed.

Standard-library reproduction from any working directory, with the frozen parent inventory installed:

```sh
python /path/to/complete_bound_unit_scout.py \
  --root /path/to/native-stream-queue \
  --expect /path/to/complete_bound_unit_scout.json
```

`--output FILE` writes the deterministic receipt. The supported interface is this authenticated CLI; internal source-building helpers are scout routines, not a hostile-input public compiler contract. The original archives, parent sources, and repository files were not edited.
