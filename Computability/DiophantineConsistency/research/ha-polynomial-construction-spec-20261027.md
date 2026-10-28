# Mathematical specification of the external construction chain

**decimal215 halts on the blank tape ⇒ the literal 14-variable polynomial has a positive zero**

Read-only extraction from `C:\ProveIt`, 2026-10-27. `L = Computability/DiophantineConsistency/Lean/DiophantineConsistency`;
paths below are relative to `L` unless stated. Companion of `poly_soundness_spec.md` (same scratchpad); its §0
(transfer of (a)-facts by Σ0-absoluteness / Σ1-completeness), §2 (constants ρ = 2^47, d = width = 94517 = 47·2011,
β = ρ^2011−1, `lowSupport` S, `lowPort`, `highPort`, kernel K, cell layout, tile table, machine) and §7 (cyclic indexing) are
assumed and not repeated. Classification is the same: **(a)** finite/local, transferable; **(b)** global, needs internal induction.

External entry: `CurrentPositiveZero2011.not_conZFC_positive_zero` (`CurrentPositiveZero2011.lean:66`) =
`CurrentHaltPacking2011.halt_constructs_packing` (`CurrentHaltPacking2011.lean:48`) + `packingData` (`CurrentPositiveZero2011.lean:22`)
+ `NativePositiveSourceConstruction.population_positive_polynomial_zero` (`NativePositiveSourceConstruction.lean:244`).
`halt_constructs_packing` = `WangTiles942ControllerDimensions.exists_controller_marked_word` (`:84`) +
`CurrentRankCalibration2011.exists_rank_forced_packing` (`:91`).

---

## 1. The chain at a glance

```
∃T  run(T).state = halt                                  (ArithmeticMachineRun215: internal run)
  │ Stage M  trace box, head positions                    (b) elementary
  ▼
Stage W  tiling word a : Z/N → [0,942), MarkedWord(N, s, a)   N = p^(m+1), s = p^ω, p = 120199
  │      explicit helical quotient of a finite computation band;  per-pair checks (a), Δ0 definition (b)
  ▼
Stage P  packing: Boolean cell word c (dummy set S, marker), C, F, α, z, J, all masks
  │      per-cell normalization (a);  base-B block sums, AND/σ concatenation, cyclic congruence (b)
  ▼
Stage R  rank R = windowRank(q,C,F,lowPort,highPort+β,J);  σ₂R = 3u+2, R ≡ 3 (4), R > 2u     (b) + (a)
  │
Stage K  controller: choose S so that R ≡ d·s (mod d·N); t := R/d − N; w := 2^(R−u)            (b) number theory
  ▼
Stage S  outer Pell seed from (u, R): s_Y, Y, a, k, c, D, τ, h, η, ζ, γ          (b) Kummer + Pell sandwich
Stage X  auxiliary Pell seed f, i, T, V, y            (ALREADY INTERNAL: ArithmeticPellAuxiliarySeed.auxiliary_seed)
  ▼
14 positive coordinates, P=Q=U=W=index=1, Z=δ  ⇒  value = 0                                   ring identities
```

Important simplifications found while reading (detailed in §10):

* **Unique Start is not needed** for the polynomial. `ExistsPacking` carries `∀z, a z = 0 ↔ z = 0`, but
  `not_conZFC_positive_zero` discards it, and no mask proof uses it (`predecessor_not_start`, `CurrentWordOrigin2011.lean:87`, uses
  temporal matching only).
* **No cyclic carries are needed.** In the constructed word every cell normalizes with carry-in 0 and carry-out 0
  (`low_carry_zero` `CurrentWordClause2011.lean:96`, `top_carry_digits` `CurrentWordTopBounds2011.lean:190`). Hence the normalized
  transport word is the *ordinary* number `F = Σ_j B^j D_j` with per-cell blocks `D_j < B`, and the Knaster–Tarski carry
  (`NativeCyclicCarry.exists_bounded_carries`, `NativeCyclicCarry.lean:37`) can be skipped entirely.
* **MarkedWord at the derived stride t is not needed.** Only scalar equations reach the polynomial, and the multiplier
  `w = B^t` agrees with `B^s` modulo `q−1`.

---

## 2. Additional fixed constants (all standard)

| Name | Value | Where |
|---|---|---|
| `B` | `ρ^2011 = 2^94517` | `CurrentControllerData2011.lean:21`, `B_eq :31` |
| `p` (auxiliary) | `120199`, prime, `p = 13·9246+1`, `9246 = 23·402 = lcm(23,402)` | `:22-23`, `:46-52` |
| orders | `ord_47(2)=23`, `ord_2011(2)=402`; `gcd(23,d)=gcd(402,d)=1` ⇒ `ord_47 B = 23`, `ord_2011 B = 402` | `:62-100` |
| residues of B | `B ≡ 37 (47)`, `≡ 1283 (2011)`, `≡ 37435 (p)` | `:102-115` |
| lift | `B^(p−1) ≡ 7300767062 = 1 + 60739·p (mod p²)`, so `p ∥ B^(p−1) − 1` | `:139-155` |
| residues of K | `K ≡ 26 (47)`, `≡ 1995 (2011)`, `≡ 114787 (p)` | `CurrentKernelResidues2011.lean:162-164` |
| coupling | `1 + B·K + B² ≡ 29 (47)`, `674 (2011)`, `36379 (p)` | `CurrentControllerData2011.lean:162-167` |
| `C0` | `d·p = 94517·120199` | `CurrentControllerSubsets2011.lean` |

All are closed Σ1 facts about standard numbers (e.g. `∃x (x = B^(p−1) ∧ x mod p² = 7300767062)`), so they hold in V by Σ1-completeness
of Q. They are **(a)**.

Notation used below (renaming Lean's clashing names): `T` halting time; `ω` width exponent (Lean `rw`); `η_H` height exponent
(Lean `rh`); `m = ω + η_H − 1` controller exponent (Lean `k`); `N = p^(m+1)` cells; `n = 2011N` sub-positions;
`u = d·N = 47n`; `q = 2^u = ρ^n = B^N`; `s = p^ω` tiling stride; `t` final stride; `R` rank; `r = (R−1)/2`.

---

## 3. Stage M — the run and its trace box

**Statement.** Given `run(T)` halted. For every `τ`: (i) `run(τ) = run(min(τ,T))`; (ii) `|head(τ)| ≤ τ` and the head stays in
`[−T, T]`; (iii) every cell `x` with `|x| ≥ T+1` is blank at every time (`WangMachineTraceBounds.halted_trace_box`, `:132`).

**Internal setting.** `ArithmeticMachineRun215.run` (`ArithmeticMachineRun215.lean:33`) codes configurations as
`P(state, P(left, right))` (`encodeConfig`, BusyBeaver `ArithmeticMachineStepPerm252.lean:104`): state code 0 = halt, code
`q+1` = state q; `right` bit 0 is the scanned cell; `left` bit 0 is the cell left of the head. Step (`numericStep`,
`ArithmeticMachinePerm252.lean:78`): move right `⟨q', 2·left+w, right/2⟩`; move left `⟨q', left/2, left%2 + 2(w + 2·(right/2))⟩`.
The absolute head is **not** stored. Define `head(0)=0`, `head(τ+1) = head(τ) ± 1` (by the action looked up from `run(τ)`; unchanged if halted) by a second PR blueprint, and
`tape(τ,x) = fbit(right, x−head)` for `x ≥ head`, `fbit(left, head−1−x)` for `x < head`.

**Proof idea.** (i) is `ArithmeticMachineTape215.runFrom_halted` (`:211`), already internal. (ii)–(iii): induction on τ of
`|head(τ)| ≤ τ ∧ ‖left(τ)‖ ≤ τ ∧ ‖right(τ)‖ ≤ τ+1`-type bit-length bounds, from the two step formulas. **(b), elementary.**
The tape-reading identities (`tape(τ+1, x)` after a step equals the written bit at the old head and `tape(τ,x)` elsewhere) are
Δ0 bit lemmas about `2l+w`, `l/2`, `l%2` — **(b), elementary**, and are the only machine semantics Stage W needs.

---

## 4. Stage W — the tiling word

### W1. Dimensions (`WangTiles942PowerDimensions.lean:39`, `WangTiles942ControllerDimensions.lean:55`)

Lean picks, with `wBound = 0` and height bound `max(0,p²) = p²`:

* `ω = 2T+5`, `η_H = T + p² + 5`, `m = ω + η_H − 1 = 3T + p² + 9`
* width `w = p^ω`, height `H = p^(η_H)`, `N = w·H = p^(m+1)`
* margins `L = T+2` (left), `R' = w − L` (right)

Needed only: `w ≥ 2T+4`, `H ≥ T+2`, `H ≥ 3`, and for the controller `ω < m` and `d·p < p^m`
(`controller_exponents`, `:41`). Existence of these powers is totality of exponentiation in IΣ1.

### W2. The finite band (`WangTiles942CycleBand.lean:47-63`, `WangTiles942TraceCycle.lean:24,82`)

For a row index `k ∈ [0,H)` and column `x ∈ [−L, R')`:

```
band(x,k) = seam(k)                if x = −L
          = cycleTile(k, x)        otherwise
seam(k)   = ⟨edgeCode(k−1)², 437, edgeCode(k), 437⟩,   edgeCode(k) = 2 if k=0, 1 if k=H−1, else 0
cycleTile(k,x) = initialTile(x)                  k = 0
               = resetTile(x) = ⟨1,438,1,initialTile(x).north⟩     k = H−1
               = finishTile(run k, x) = ⟨0, color(run k,x), 0, 438⟩  k = H−2
               = runTile(k, x)                   otherwise
initialTile(x) = ⟨2,434,2,0⟩ (x<0), Start ⟨2,435,3,1⟩ (x=0), ⟨3,436,4,4⟩ (x=1), ⟨4,436,4,0⟩ (x>1)
runTile(k,x)   = passTile ⟨0,color,0,color⟩ if run(k) halted, else stepTile(run k, q, x):
     x = head:      transitionRow(2q + bit).tile                     (WangTiles942TableData.lean:23)
     x = nextHead:  receive ⟨d·rail(d,q'), b, (1−d)·rail(d,q'), headColor(q',b)⟩, (w,d,q') = action(2q+bit)
     else:          ⟨0, b, 0, b⟩,  b = tape bit at x
```

(`WangTiles942FinishConstruction.lean:22,26,70,129`, `WangTiles942StepConstruction.lean:30,38`.) `color(cfg,x)` is
`headColor(state, bit) = 2·state + bit + 2` at the head (halt = state 215) and the bit elsewhere (`WangMachineEncoding.lean:88`).

**Facts (`band_properties`, `CycleBand.lean:117`).** All tiles Allowed; vertical matching `band(x,k+1).north = band(x,k).south`
cyclically in `k`; horizontal matching for `x ≥ −L`; the **twisted seam** `band(−L,k+1).west = band(R'−1,k).east`; `band(0,0) = Start`.
The boundary colours come from the trace box: columns `−L+1` and `R'−1` are blank pass cells in every run row
(`CycleBoundary.lean:23,67,79`), giving west 2/1/0 and east 4/1/0 = edgeCode² in init/reset/other rows.

### W3. The helical quotient (`WangTiles942HelicalExtension.lean:18-26`, `WangTiles942HelicalQuotient.lean:69`)

For `z ∈ [0,N)` put

```
x(z) = ((L − z) mod w) − L ∈ [−L, R'),     τ(z) = ⌊(L − z)/w⌋ ∈ [−H, 0],
a(z) = index of the tile band(x(z), τ(z) mod H) in the 942-table.
```

Then `−x(z) − w·τ(z) = z`, so `a(address(x,τ)) = band` with `address(x,τ) = −x − wτ` (`WangTiles942Periodic.lean:29`).

**Statement (`marked_word_of_halt`, `CycleBand.lean:136`; `canonical_unique_word_of_halt`, `BandMarker.lean`).**
`MarkedWord(N, w, a)` (`WangTiles942Periodic.lean:23`):

* `a(0) = 0`
* `East(tile a(i)) = West(tile a(i−1))`
* `South(tile a(i)) = North(tile a(i−w))`

and, unused downstream, `a(z) = 0 ⇔ z = 0` (`band_eq_start_iff`, `BandMarker.lean:31`).

**Proof idea.** `a(0)`: `x=0, τ=0`, so the tile is `initialTile(0)` = Start. Horizontal: `z−1` corresponds to `(x+1, τ)` unless
`x = R'−1`, in which case it corresponds to `(−L, τ+1)` (helix); the first case is band horizontal matching, the second is the
twisted seam. Temporal: `z−w` corresponds to `(x, τ+1)`; vertical matching, with `τ mod H` wrapping reset→initializer.
The tile facts are **(a)**: for each state q < 215 and bit, the transition/receive/pass tiles agree on shared edges
(`stepTile_horizontal`, `StepConstruction.lean:139`), `stepTile.north = color(cfg)`, `stepTile.south = color(step cfg)`
(`:85,99`), the rails are ≥ 6 so the walls never see them, and every constructed tuple is one of the 942 table tiles
(`allowed_iff_tile`). The glue "which x is the head / next head and what bit is read" uses Stage M's tape-reading identities.

**Internal.** `a` is Δ0 in the code of the run sequence `⟨run(0..T), head(0..T)⟩` (coded by Σ1-collection) and `T, L, w, H`;
the 942-index lookup is a standard finite table. The three MarkedWord clauses are `∀ i < N` statements proved by case
analysis on `(x(i), τ(i))`, not by induction. Everything with `z−1`, `z−w` mod N uses `N = wH` and Euclidean division by `w`.
**(b), elementary; the tile facts are (a).**

---

## 5. Stage P — the packing (`CurrentNativePacking2011.marked_constructs_packing`, `:65`)

Inputs: MarkedWord `(N, s, a)` with `s = p^ω`, a Boolean dummy map `δ : Z/N → {0,1}` (later `δ = 1_S`).

### P1. The Boolean word (`CurrentWordConstruction2011.lean:27-34,172`; `CurrentWordCopies2011.lean:26`)

* **Marker**: `μ(j) = [a(j+s) = 0]` (`shiftedStartMarker`). With unique Start this is the single cell `−s`, but uniqueness is
  never used.
* **Cell type** `x_j = (a_j, δ_j, μ_j)`. The cell contents are `Cell(x) = Σ_{e<2011} c_e ρ^e`, where
  `c_e = localDigit(i, e)` (`CurrentCellConstruction2011.lean:46`):
  - selector `[e = physicalPosition(i)]` for `e < 942`
  - complemented label bits at South `942..950`, North `960..968`, East `969..976`, West `978..985`
  - `c_977 = δ`, `c_1004 = μ`
  - 0 elsewhere
* `c_k` for `k = 2011j + e` is `Cell(x_j)`'s digit `e`. So `C := source = Σ_k c_k ρ^k = Σ_{j<N} B^j·Cell(x_j)`.

`Cell(x) < ρ^1005`, it is supported on `S`, `c_0 = [a_j = 0]`, and the selector count is exactly 1.

### P2. Raw transport digits and the per-cell normalization — (a)

`raw_k = conv(folded, c)_k + c(k − 2011s)` (`CurrentCarryConstruction2011.lean:24`, with `W = displacement(s) = 47·2011·s`,
`CurrentWordClause2011.lean:29`; at a whole-cell displacement the binary rotation is the plain index shift, `rotation_whole :78`).
By the support pattern (soundness spec B0), `raw` at cell j reads only cells `j−1` (bare-2020 source), `j`, and `j−s`.
So the block

```
Raw_j := Σ_e raw_{2011j+e} ρ^e = Lo(x_j) + Hi(x_{j−1}) + Cell(x_{j−s}),
```

where `K·Cell(x) = Lo(x) + B·Hi(x)` is the split of the polynomial product (in ρ) at degree 2011. This is an exact identity per
cell type.

Call a triple `(x_prev, x_cur, x_tmp)` **admissible** when:

* `East(a_cur) = West(a_prev)`
* `South(a_cur) = North(a_tmp)`
* `μ_tmp = [a_cur = 0]`

Every cell's triple `(x_{j−1}, x_j, x_{j−s})` is admissible by MarkedWord and the definition of μ (`south_pair`, `horizontal_pair`,
`marker_pair`, `CurrentWordCopies2011.lean:56-93`).

**Local Normalization Lemma (LNL).** For every admissible triple, the carry chain `κ_{−1}=0`,
`κ_e = ⌊(raw_e + κ_{e−1})/ρ⌋` satisfies all of the following:

1. `κ_e ≤ 57`, by the budget `raw + 57 < 58ρ` (`carry_budget`; kernel mass, soundness spec §2).
2. `κ_e = 0` for `e ≤ 1004` (`low_carry_zero`).
3. `κ_2009 = κ_2010 = 0` and `d_2010 = 0` (`top_carry_digits`).

Hence `Raw = D := Σ_e d_e ρ^e < ρ^2010`. Moreover:

* **masks:** `d_e AND cellDigit(e) = 0` for all e. The cases are:
  - origin `e=0`: `d_0 = [a_tmp = 0]`, at most 1 against mask 4 (`normalized_origin`, `CurrentWordOrigin2011.lean:60`)
  - padding `1..916`: bit 3 is clear because `raw mod 2048 ≤ 5` (`CurrentWordPadding2011.lean:132`)
  - copies `960..968` and `987..994`: the digit is even (`south_mask_pass`, `horizontal_mask_pass`)
  - marker `1004`: the digit is even (`marker_mask_pass`)
  - clause `1005`: `d_1005 = 2^45 + 2 + c_1` (`normalized_clause`, `CurrentWordClause2011.lean:110`)
* **origin variant:** if additionally `a_cur = 0`, then `a_tmp ≠ 0` (`North(a_tmp) = South(Start) = 1 ≠ 435`), so `d_0 = 0`.
  This meets the origin mask 3 (`predecessor_not_start`, `:87`).
* **low mask:** `Cell(x) AND lowPort = 0`. If `a = 0`: `Cell(x)` is odd and `(Cell(x)−1) AND (lowPort+1) = 0`.
* **positivity:** `d_1005 ≥ 2^45`.

**Classification.** All quantifiers range over standard finite sets (`a_* < 942`, `δ, μ ≤ 1`), and every number involved is a
standard number below `B²`. The LNL is a single closed Δ0 sentence with standard parameters, true in ℕ, hence true in V
(soundness spec §0). **(a).** The Lean proofs (`CurrentWordCopies2011`, `CurrentWordPadding2011`, `CurrentWordClause2011`,
`CurrentWordOrigin2011`, `CurrentWordTopBounds2011`) are stated for a global carry solution of a global word. A local restatement over
triples is a mechanical re-packaging of the same `omega`/bit arguments.

### P3. The scalars (`CurrentWordScalarWitness2011.lean:22-34,67`)

With `D_j := Raw_j` (P2):

| Scalar | Definition | Notes |
|---|---|---|
| `F` (normalized) | `Σ_{j<N} B^j D_j` | `0 < F < q/ρ`, ordinary number (P2 + base-B bounds) |
| `C` | `Σ B^j Cell(x_j)` | `0 < C < ρ^(n−1006)` |
| `α` | `q − C − F` | `> 0` |
| `J` | `rep_d(N) = Σ_{i<N} 2^(d·i)` | `βJ + 1 = q` (`ArithmeticRepunit.repunit_identity`, **internal**) |
| `z` | `⌊(K + B^s)·C/(q−1)⌋ + 1` | see transport below |

**Transport (b).** `(K + B^s)·C ≡ F (mod q−1)`:

* `K·C = Σ_j B^j Lo(x_j) + Σ_j B^(j+1) Hi(x_j)`
* `B^s·C = Σ_j B^(j+s) Cell(x_j)`
* `B^N = q ≡ 1`, so `Σ_j B^(j+e) y_j ≡ Σ_j B^j y_(j−e mod N)` for `e = 1` and `e = s`

The cyclic-shift lemma for represented base-B sums is **(b)**, by induction on N, or by splitting the sum at `N−e`.
Since `0 < F < q−1`, F is the residue, so `(K+B^s)C = F + (z−1)(q−1)` and the transport factor
`(K+w)C + (q−F) − z(q−1) = 1` (`transport_factor_eq_one`, `:52`).

**Masks (b), from (a) blocks.**

* `F AND (highPort·J − 1) = 0`: `highPort·J − 1 = Σ_j B^j (highPort − [j=0])`, with no borrow beyond block 0 because
  `highPort ≡ 4 (mod 8)`.
* `(C−1) AND (lowPort·J + 1) = 0`: `lowPort·J + 1 = Σ_j B^j (lowPort + [j=0])`.

Both reduce to the block lemma `(Σ B^j x_j) AND (Σ B^j y_j) = Σ B^j (x_j AND y_j)` for `x_j, y_j < B`: an fbit lemma by
induction on N, **(b)**. Then apply the LNL blockwise.

---

## 6. Stage R — rank, population, parity (`CurrentPackingRank2011.lean:23-27,107`; `CurrentPackingParity2011.lean:53`)

`R := windowRank(q, C, F, lowPort, highPort+β, J) = (q(q−F) − C)(q²−1) + (lowPort + q(highPort+β))J`
(`NativeRankVariation.lean:20`). For `0 < C`, `C + F < q` this equals the natural number

```
fourBlocks = (C−1) + (lowPort·J+1) + q·(F + highPort·J − 1) + q²·(q−C) + q³·(q−F−1)
```

(ring identity using `βJ = q−1` once; `fourBlocks_cast :55`).

* **σ₂(R) = 3u+2 (b).** The two AND-disjointness facts give additivity inside blocks 1 and 2
  (`ArithmeticBinaryCarry.population_add_eq_iff`, **internal**). Blocks concatenate (`ArithmeticBinaryPopulation.concatenate`,
  **internal**). Complements give `σ(q−1−A) = u − σ(A)` (`complement`, **internal**). Finally
  `σ(lowPort·J+1) + σ(highPort·J−1) = N(σ lowPort + σ highPort) + 2 = u + 2`, by `population_repeat` (**internal**,
  `ArithmeticRepunit.lean:76`), with the standard-constant facts `σ lowPort + σ highPort = 94517`, `lowPort` even and
  `highPort ≡ 4 (mod 8)` (**(a)**; prove digitwise, see soundness A5).
  Total: `σ(C−1) + σ(M) + σ(F) + σ(H) + (u − σ(C−1)) + (u − σ F) = 3u+2`.
* **R ≡ 3 (mod 4).** `C−1 ≡ 0 (mod 4)` by the low mask, `lowPort·J+1 ≡ 3 (mod 4)`, and `4 | q`. **(b), easy.**
* `2u < q³ ≤ R`. **(b), easy.**

---

## 7. Stage K — rank calibration (`CurrentRankCalibration2011.lean:44,91`)

The polynomial forces `w·q = 2^R`, i.e. `w = 2^(R−u)`. But w must also be the transport multiplier of the same word,
`w ≡ B^s = 2^(ds) (mod q−1)`. Hence we need

```
d | R   and   R/d ≡ s (mod N),   i.e.   R ≡ d·s (mod d·N).          (★)
```

R depends on the word chaotically, so (★) is forced by a **controller**: dummy bits at safe cells change R by an exactly
known amount.

### K1. Exact rank variation (b)

Let `P(S) = Σ_{j∈S} B^j` and `A = K + B^s`. Safety means `0 < j`, `j+1 < N` and `j+s < N` for all `j ∈ S`, so no block
contribution wraps (`CurrentControllerPositions2011.lean:137-170`). Under safety:

* `C(S) = C(∅) + ρ^977·P(S)`
* `F(S) = F(∅) + A·ρ^977·P(S)`, exactly. The block formula of P3 is non-cyclic for the changed terms.
  Lean's indirect route (two normalizations + `nonwrap_of_short`, `CurrentDummySafety2011.lean:130-169`) is unnecessary with
  §5's explicit F.
* **Rank variation (ring identity):** `R(S) = R(∅) − Γ·P(S)`, where
  `Γ = ρ^977 (q²−1)(1 + q·A)` (`rank_power_variation`, `NativeRankVariation.lean:47`; `Gamma`, `CurrentControllerUnits2011.lean:24`).

### K2. Γ is a unit mod d·N (b, short)

Since `p ≡ 1 (mod 23)`, `(mod 402)`, and `B^p ≡ B (mod p)`, we get `B^p ≡ B` modulo 47, 2011 and p (standard, (a)). By induction on n,
`B^(p^n) ≡ B` modulo each of them (`pow_pow_fixed`, `CurrentControllerUnits2011.lean:42`). So `q = B^N` and `B^s` reduce to B.
Then `q² − 1 ≡ 5, 1090, 99282` and `1 + qA ≡ 1 + BK + B² ≡ 29, 674, 36379`, all nonzero, and ρ is odd. Hence
`gcd(Γ, 47·2011·p^(m+1)) = 1` (`coprime_Gamma_width_cells`, `:170`).

### K3. The controller subset (`CurrentSafeController2011.exists_safe_gamma_sum`, `:74`)

**Target.** `θ := Γ^(−1)·(R(∅) − d·s) mod d·N`. We seek a safe S with `|S| ≤ d·p` and `P(S) ≡ θ`.

**Construction** (`CurrentControllerSubsets2011.lean:93`, `ControllerResidueLift.lean:42`, `ControllerAuxiliaryChoice.lean:27`,
`ControllerIntervalSums.lean:47-70`, `CurrentControllerPositions2011.lean:13,107,146`):

1. **Normalize.** `θ' := B^(−2)·θ (mod d·N)`; B is a unit since dN is odd.
2. **Boolean term.** Choose `ε ∈ {0,1}` with `θ' − εB ≢ 0 (mod p)`; possible since `B ≢ 0 (mod p)`.
   Put `a := (θ' − εB) mod C0`. Then `0 < a < C0` and `p ∤ a`.
3. **Coordinates.** `g := B^(p−1)`. Then `g ≡ 1 (mod C0)` and `ord_{dp^(m+1)}(g) = p^m` (§8.2). The map
   `j ↦ zc(j) := (g^j − 1)/C0 mod p^m` is a bijection of `Z/p^m` (`exists_power_coordinates`, `ControllerPowerCoordinates.lean:10`);
   write `e = zc^(−1)`.
4. **Interval.** `υ := (θ' − εB − a)/C0 mod p^m`, and
   `start := a^(−1)·(υ − a(a−1)/2) mod p^m` (a is a unit mod p^m). The interval `I = {start, …, start + a − 1}` in `Z/p^m`
   has a distinct elements (`a < C0 < p^m`) and `Σ_{z∈I} z = υ`.
5. **Positions.** `S = {2 + (p−1)·e(z) : z ∈ I} ∪ ({3} if ε = 1)`. These are distinct, `≠ 3`, `< p^(m+1)`, and safe because
   `ω < m` (`position_budget :24`).
6. **Check.** `Σ_{j∈S} B^j = B²(Σ_{z∈I} g^(e z) + εB) = B²(a + C0·υ + εB) ≡ B²θ' = θ`.

Then `R(S) = R(∅) − Γ·P(S) ≡ d·s (mod d·N)`, which is (★).

### K4. Derived stride and multiplier (`CurrentRankStride2011.lean:16-63`, `ControllerRankStride.lean:12-66`)

`t := R/d − N`. By (★) and `R > 2dN` we have `d·t = R − u`, `t > N`, `t ≡ s (mod N)`. Set
`w := 2^(R−u) = 2^(d·t) = B^t` and `forced_product: w·q = 2^R`. Because `t ≡ s (mod N)` and `B^N = q ≡ 1 (mod q−1)`,
`B^t ≡ B^s`. So P3's transport holds with w; take `z := ⌊(K+w)C/(q−1)⌋ + 1`, where `(K+w)C ≡ F` as before. **(b), easy.**
(Lean also re-proves the whole packing and MarkedWord at stride t, `CurrentWordRephase2011.lean:83-116`; not needed.)

### K5. Output of Stages W–K (= `ExistsPacking`, `CurrentHaltPacking2011.lean:26`; `packingData`, `CurrentPositiveZero2011.lean:22`)

`u = d·N > 0`, `J, F, α, z, w, C > 0`, and:

* `βJ + 1 = 2^u`
* `C + F + α = 2^u`
* `w·2^u = 2^R`
* `(K+w)C + (2^u−F) − z(2^u−1) = 1`
* `windowRank(2^u, C, F, lowPort, highPort+β, J) = R`
* `σ₂R = 3u+2`, `R ≡ 3 (mod 4)`

This is exactly `NativePositiveSourceConstruction.Data` (`:24`) plus the two rank facts.

---

## 8. Number-theoretic facts used in Stage K

### 8.1 Statements

1. **(LTE)** `p ∥ g−1` ⇒ `p^(k+1) ∥ g^(p^k) − 1`, hence `ord_{p^(k+1)}(g) = p^k` (`PrimePowerOrder.lean`; `CurrentAuxiliaryOrder2011.lean:47-55`).
   Lean uses Mathlib `emultiplicity` / `Nat.emultiplicity_pow_sub_pow`.
2. **CRT for orders.** `ord_{d·p^(m+1)}(g) = lcm(ord_d g, ord_{p^(m+1)} g) = p^m`, since `g ≡ 1 (mod d)` (`CurrentPowerCoordinates2011.lean:50`).
3. **Affine coordinates.** `g^j ≡ 1 (mod C0)` for all j, and `j ↦ (g^j−1)/C0` is injective on `[0,p^m)` because the order is p^m.
   Surjectivity follows from Finite injective ⇒ bijective (`ControllerPowerCoordinates.lean:10-40`, **pigeonhole**).
4. Modular inverses mod `p^m` and `d·N` (Bezout).
5. `B^(p^n) ≡ B (mod 47, 2011, p)` (K2).

### 8.2 Internal routes

* **LTE (b).** Prove by induction on n: `(1+x)^n = 1 + n·x + binom(n,2)·x² + x³·M_n` for some `M_n`, using a represented
  `binom(n,2) = n(n−1)/2`. Then:
  - with `g = 1 + p·v`, `p ∤ v`: `g^p = 1 + p²v'` with `v' ≡ v (mod p)`, since p is odd and `p | binom(p,2)`;
  - iterating, by induction on k: `g^(p^k) = 1 + p^(k+1)·v_k` with `v_k ≡ v (mod p)`.
  Order exactly `p^m` modulo `p^(m+1)` then needs only "`ord | p^m` and `ord ∤ p^(m−1)`". No `emultiplicity`.
* **Surjectivity of coordinates: replace pigeonhole by a Hensel induction (b).**
  Claim: `∀ z < p^k ∃ j < p^k: g^j ≡ 1 + C0·z (mod d·p^(k+1))`.

  *Step k → k+1.* Given z, first get j with `g^j ≡ 1 + C0·z (mod dp^(k+1))`. The quotient `(1 + C0·z)·g^(−j)` is
  `≡ 1 + dp^(k+1)·y (mod dp^(k+2))`. Multiply by `(g^(p^k))^l = 1 + l·dp^(k+1)·v + …`, with
  `l ≡ y·v^(−1) (mod p)`. The new exponent `j + l·p^k < p^(k+1)` works.

  The formula has only bounded quantifiers over a Δ1 matrix (modular powers), so IΣ1 induction applies. This avoids coding
  the whole coordinate permutation.

  (Alternatively IΣ1 proves PHP for coded injections `[0,M) → [0,M)` by Δ0(exp)-induction, after coding the Σ1-definable map by
  Σ1-collection.)

---

## 9. Stages S and X — Pell witnesses and the 14 coordinates

### S. Outer seed (`NativeOuterSeedConstruction.exists_outer_seed`, `:153`; structure `Seed`, `:118`)

Inputs: `u > 0`, `R = 2r+1`, `σ₂R = 3u+2`. Put `X = 2^R`.

**Step 1 — sizes (`population_sizes`, `:21`).** `σ(r) = 3u+1` (because `σ(2r+1) = σ(r)+1`), `r ≥ 4`, `3u+1 < R`. **(b), easy.**

**Step 2 — half floor (`scaled_half_floor`, `:32`; `Ratio90.binomial_floor_two`, `HilbertTenthProblem/…/PellRatio90.lean:373`).**

```
Q := ⌊(X+1)^(2r) / X^r⌋,   v := (X+1)^(2r) − Q·X^r,   4v < X^r,   Q = binom(2r,r) + w'·X.
```

Kummer `lemma_2_15` gives `2^(3u+1) | binom(2r,r)` (since `σ(r) ≥ 3u+1`). Also `2^(3u+1) | X`. Hence:

* `Y := Q/2`
* `s_Y := Q / 2^(3u+1)`
* `Y = s_Y·q³`, with `q = 2^u`

**Step 3 — Pell data.**

| Symbol | Value |
|---|---|
| `a` | `Y(X+1)` |
| `A` | `a+2` |
| `P` | `2XY²+1` |
| `K₀` | `y_{r+1}(P)` |
| `k` | `2K₀` |
| `τ` | `x_{r+1}(P)` |
| `c` | `y_R(A)` |
| `D` | `x_R(A)` |

Base convention: Pell base A means `x² − (A²−1)y² = 1`; internal `ycoord n b` has base `b+2`.

**Step 4 — interval (`pell_interval`, `:68`).** `kY < c < k(Y+1)`. Put `η := c − kY` and `ζ := k − η`; both are positive.

The proof goes through the ratio `ξ = (X+1)^(2r)/X^r = Q + v/X^r`:

* lower bound `K₀(X+1)^(2r) < c·X^r` (`Ratio90.lower_estimate`) — Pell growth `c ≥ (2A−1)^(2r)`,
  `K₀ ≤ (2P)^r` and `2P(X+1)² < (2A−1)²X`;
* upper bound `c/K₀ < ξ + 1` (`NativeHalfBinomial.upper_estimate_scaled`, `:18`) — growth bounds, `(1+ε)^r ≤ 1 + 2rε`
  with `ε = 9/(Y(X+1))`, `72r < X+1`, `16 ≤ Y(X+1)`, `ξ < 2(Y+1)`.

Since `ξ/2 ∈ [Y, Y + 1/8)`, it follows that `c/k ∈ (Y, Y+1)`.

**Step 5 — index.** `k ≡ R+1 (mod E)` with `E = XY`, because `y_n(P) ≡ n (mod P−1)` and `E | P−1 = 2XY²`. So
`h := (k − R − 1)/E > 0`. **Internal:** `ArithmeticPellCongruences.residue_quotients`.

**Step 6 — root.** `D = X + a·c + γ(4a+3)` with `γ > 0`. **Internal:** `ArithmeticPellPowerRecovery.projection_quotient`
gives `x_R(a) = 2^R + a·y_R(a) + (4a+3)·z`. Positivity follows from `D ≥ (a+1)c` and `c > X`.

**Step 7 — norms.** `τ² = 1 + XY²(XY²+1)k²` (from `P² − 1 = 4·XY²(XY²+1)`) and `D² = 1 + ((a+2)² − 1)c²`.
**Internal:** `ArithmeticPellRecurrence.norm`.

**Classification.** Steps 5–7 are internal already. Steps 2 and 4 are the substantive open **(b)** work. They are shared with
soundness-direction A6, and the proposal is `research/arithmetic-half-binomial-population-proposal.md`.

### X. Auxiliary seed — already internal

`ArithmeticPellAuxiliarySeed.auxiliary_seed` (`:208`) with `R ≡ 3 (mod 4)` and `c = y_R(A)` gives:

* `f = x_{R·c}(A)`, `y_{R·c}(A) = i·c²` (`strong_seed`, `ArithmeticPellSquaredSeed.lean:83`)
* `S_x := δ·i·c²`, with `δ = A² − 1`
* `y_x := y_R(S_x)`
* `x_R(S_x) = S_x·V`
* `f²cT = V + c + f²R`

Hence `V = f²(cT − R) − c`, `f² − δ(ic²)² = 1` and `S_x²(V² − y_x²) + y_x² = 1`. External counterpart:
`ThirteenFreshSeed.auxiliary_exists` (`ThirteenFreshSeed.lean:74`), which uses `b = 1`, an arbitrary t with `c² | y_t` and
`y = −y_R(S_x)`.

### Assembly (`NativePositiveSourceConstruction.exists_construction`, `:152`; `Carrier66.canonical_drops_to_positive_zero`, `Carrier66.lean:195`)

Ports `(β, K, lowPort, highPort+β)` (`CurrentMaskData2011.lean:31`). The 14 coordinates (`Carrier65.core`, `Carrier65.lean:50`;
`Carrier66.drop`, `Carrier66.lean:22`):

| v | value |
|---|---|
| 0 J | `rep_d(N)` |
| 1 F | `Σ B^j D_j` (with dummy S) |
| 2 α | `2^u − C − F` |
| 3 z | `⌊(K+w)C/(2^u−1)⌋ + 1` |
| 4 f | `x_{Rc}(A)` |
| 5 i | `y_{Rc}(A)/c²` |
| 6 T | aux quotient |
| 7 s | `s_Y = Q/2^(3u+1)` |
| 8 w | `2^(R−u)` |
| 9 n | `(τ − k + R)/E = (τ−1)/E − h` (`FirstPellCarrier.restore_carrier`, `:115`) |
| 10 η | `c − kY` |
| 11 ζ | `k − η` |
| 12 y | `y_R(S_x)` |
| 13 γ | as in Step 6 |

Then `Carrier65.core` gives the following blocks:

* `q = βJ+1 = 2^u`, `C = q−F−α`
* `X = wq = 2^R`, `Y = s·q³`, `E = XY`, `k = η+ζ`, `c = kY+η`
* `a = E+Y`, `δ = a² + 4a+3`, `D = X + ac + γ(4a+3)`
* rank = R
* `τ = E·n + k − R = x_{r+1}(P)`

The factor values are all ring identities from S and X:

* `P = τ² − ℓ(ℓ+k) = 1`, with `ℓ = EkY`
* `Q = D² − δc² = 1`
* `U = 1`, `W = 1`, `Z = δ`

`Carrier66.index = k − hE − R = 1` is the restore condition. So
`value = P·Q·U·W·Z − δ = 0`, and all 14 coordinates are positive. **Ring algebra + positivity, (a)-trivial.**

---

## 10. Where nonstandard sizes enter

| Quantity | Size | Facts needed |
|---|---|---|
| T | arbitrary halting time | run coded up to T (Σ1-collection); trace box (b) |
| L, w, H, N | `T+2`, `p^(2T+5)`, `p^(T+p²+5)`, `p^(3T+p²+10)` | exp totality; `w ≥ 2T+4`, `H ≥ T+2` |
| n, u, q | `2011N`, `dN`, `2^u = B^N` | block sums of length N; `B^N ≡ 1 (mod q−1)` |
| C, F, J | `< q` | base-B block lemmas: value, AND, σ, cyclic shift |
| R | `∈ [q³, q⁴)` | fourBlocks identity, population (b) |
| S ⊂ [0,N) | `|S| ≤ dp` (standard), positions nonstandard | LTE, Hensel discrete log, inverses mod `p^m` and `dN` |
| t | `R/d − N` | (★) |
| r, X = 2^R | double/triple exponential in N | Kummer for `binom(2r,r)`, binomial floor, Pell growth, integer Bernoulli |
| Y, a, P, indices R, r+1, Rc | astronomically large | Pell recurrences (internal), sandwich (open) |

No fact about N beyond its being a power of the fixed prime p is used. In particular, no existence-of-N-with-prescribed-residues
theorem is needed: the residues of q are forced by `B^p ≡ B`. Conversely, Kummer is used only in the direction
`σ(r) ≥ n ⇒ 2^n | binom(2r,r)`. The soundness direction uses the other direction.

---

## 11. Hardest internal obligations and proposed simplifications

### Ranked obligations

1. **Outer-seed sandwich and Kummer (Stage S, Steps 2 and 4).** This needs a represented binomial table (Pascal PR), the
   binomial theorem for `(X+1)^(2r)`, symmetry `2Σ_{m<r} binom(2r,m) = 4^r − binom(2r,r)`, Legendre for 2
   (`v₂(n!) = n − σ(n)`, by induction using `σ(n+1) = σ(n) + 1 − v₂(n+1)`, hence `v₂ binom(2r,r) = σ(r)`), Pell growth
   (`y_lower`/`y_upper`, internal), and the integer Bernoulli inequality `2re ≤ a ⇒ a(a+e)^r ≤ (a+2re)a^r` (proposal).
   **Shared with soundness A6. Build it once.**
   Recommended phrasing for reuse: the *unconditional* sandwich
   `K₀(X+1)^(2r) < c·X^r` and `c·X^r < K₀((X+1)^(2r) + X^r)`, under `a = Y(X+1)`, `P = 2XY²+1`, `72r < X+1`,
   `16 ≤ Y(X+1)` and `(X+1)^(2r) < 2(Y+1)X^r`. The proposal's version assumes `c = kY+η` with `η, ζ > 0`, which the construction
   cannot supply; drop those hypotheses.
2. **Controller number theory (K2–K3, §8).** LTE by a fixed-degree expansion; Hensel-style discrete-log surjectivity instead
   of pigeonhole; inverses; the interval subset. Moderate. All with bounded quantifiers over Δ1 modular powers.
3. **Global block identities (P3, Stage R).** One generic library for `Σ_{j<N} B^j x_j` with `x_j < B`:
   - value bounds
   - fbit/AND concatenation
   - population additivity (internal pieces exist)
   - the cyclic shift congruence modulo `B^N − 1`
4. **Tiling verification (Stage W)** over nonstandard N with the represented run: head tracking, trace box, tape-reading
   lemmas; the three MarkedWord clauses by case analysis.
5. **LNL (P2)** is large, but it is (a): one closed Δ0 sentence, transferable by absoluteness once restated locally.

### Simplifications (recommended)

* **S1 — drop unique Start.** Not used by any scalar, mask or controller step.
* **S2 — blockwise normalization.** Define `F := Σ B^j(Lo(x_j) + Hi(x_{j−1}) + Cell(x_{j−s}))` and prove `F < q/ρ` from the LNL.
  This removes `NativeCyclicCarry` (Knaster–Tarski), the end-around carry, the `word ≤ ρ^n − 1` exclusion and
  `NativeCyclicCarryWord`. No global carry or digit sequence needs to be represented: the digits of F are the per-cell
  standard digits.
* **S3 — direct calibration identity.** Prove `F(S) = F(∅) + Aρ^977 P(S)` directly from the non-wrapping block formula. Lean's
  normalization-uniqueness/nonwrap argument (`CurrentDummyMutation2011`, `CurrentDummySafety2011`, `CurrentFiniteDummyMutation2011`)
  disappears. Internally: compute `R(∅)`, then θ, then S, then build the final word once with `δ = 1_S`.
* **S4 — no rephase.** Use stride s for the word and t only for `w = B^t`. Drop `CurrentWordRephase2011` and the MarkedWord at t.
* **S5 — smaller dimensions (optional).** `ω = T+1` and `η_H = T+3` satisfy every need (`p^(T+1) ≥ 2T+4`, `p^(T+3) ≥ T+2`,
  `η_H ≥ 2`, `d·p < p^m`). The Lean choice `η_H = T+p²+5` is an artifact of the generic `max(hBound, p²)` interface; it is
  harmless but makes N needlessly large.
* **S6 — construct the tableau directly from the represented run.** `a(z)` is the closed formula of W3, applied to
  `band(x, τ mod H)` with `run(min(k,T))`. No ℤ-indexed plane, `Classical.choose` or `Function.Periodic` is needed.
* **S7 — Hensel instead of pigeonhole** for the controller coordinates (§8.2).
* **The controller is unavoidable.** (★) is a self-referential fixed point: R depends on the word, and the word's
  multiplier must be `2^(R−u)`. The single free dummy slot (977) per cell is the polynomial's only knob. Making powers of B
  span every residue mod dN with a standard number of terms forces a prime-power N with a principal unit of exact order, so
  the p-adic structure in §8 is essential. What can be simplified is only the proof of discrete-log surjectivity.

---

## 12. Checklist

| Step | Content | Class | Internal status |
|---|---|---|---|
| M | run, head, trace box, tape reading | (b) elem. | run **done**; head/trace/tape lemmas needed |
| W | band, helical quotient, MarkedWord | (a) tiles + (b) case analysis | needed |
| P1 | cell word, marker, C | (a) + block sums | needed |
| P2 | LNL (masks, zero carries, clause, origin) | (a) | restate locally, transfer |
| P3 | F, α, z, transport, two masks | (b) | block library needed; repunit **done** |
| R | σ(R) = 3u+2, R ≡ 3 mod 4, R > 2u | (b) | concatenate/complement/population_add/population_repeat **done**; standard σ-constants (a) |
| K1 | `R(S) = R(∅) − ΓP(S)` | ring + (b) non-wrap | easy |
| K2 | Γ unit | (b) + (a) residues | easy |
| K3 | controller subset | (b) number theory | needed: LTE, Hensel log, inverses |
| K4 | t, w, forced product | (b) | easy |
| S1/5/6/7 | sizes, index, root, norms | (b) | **done** (congruences, projection_quotient, norm) |
| S2 | Q, Y = s·q³ via Kummer | (b) | **open**: binomial/Legendre library |
| S4 | `kY < c < k(Y+1)` | (b) | **open**: integer sandwich (proposal) |
| X | f, i, T, V, y | (b) | **done** (`auxiliary_seed`) |
| Asm | 14 coordinates, value 0 | ring | easy |
