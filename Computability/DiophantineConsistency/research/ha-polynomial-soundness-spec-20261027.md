# Mathematical specification of the external soundness chain

**Positive zero of the literal 14-variable polynomial ⇒ the decimal215 machine halts on the blank tape**

Read-only extraction from `C:\ProveIt`, 2026-10-27. Paths below are relative to
`L = Computability/DiophantineConsistency/Lean/DiophantineConsistency`. The purpose
is to let the chain be re-proved inside an arbitrary model `V ⊨ IΣ1`, starting from the
already-internal arithmetic endpoints, without re-reading the Lean.

External entry point: `CurrentSoundness2011.polynomial_zero_blank_halts` (`CurrentSoundness2011.lean:26`)
= `CurrentMarkedWindow2011.polynomial_zero_marked_window` (`CurrentMarkedWindow2011.lean:140`)
followed by `WangTiles942Soundness.marked_blank_halts` (`WangTiles942Soundness.lean:64`).

---

## 0. How to transfer the parts classified (a)

**Key observation.** In any model of Q, every element below a standard numeral is itself a
standard numeral. All per-cell data in the chain are bounded by standard constants: bits
`c_k ≤ 1`, carries `κ_k ≤ 57`, digits `d_k < 2^47`, label words `< 2^34`, selector counts `≤ 942`,
tile indices `< 942`, colors `< 512`, machine states `< 216`. So, once you fix a cell base `b`,
everything the local lemmas talk about is a standard tuple. A local lemma of the form

> for all values `x_1..x_m` below standard bounds `B_1..B_m`, `Hyp(x) → Concl(x)`

(`Hyp` and `Concl` built from `+ · ≤ div mod AND` with standard constants) is a **closed Σ0
sentence**. If its ℕ version is already a Lean theorem, it holds in `V` by Foundation's
`Definability/Absoluteness.lean:20 shigmaZero_absolute` (or `R0/Basic.lean:143
sigma_one_completeness`). Alternatively you can re-prove it symbolically in `V`: the existing
proofs are almost all `omega`/bit-test arguments with standard constants.

The only nonstandard objects are: the cell count `N` (internal `L`), the cyclic length
`n = 2011·N`, the bit-length `u = 47·n = 94517·N`, the temporal shift `W`, the stride `s`,
position indices `k, b < n`, the coded sequences `c, κ, d : [0,n) → ℕ` and `a : [0,N) → [0,942)`,
the big numbers `q, J, C, F, R, K·C, 2^W`, and the machine run up to time `N`.

**Classification used below.**

- **(a) FINITE/LOCAL:** either a property of fixed standard data (the 942-tile table, the
  kernel, the masks, the 430 decoded actions), or a statement that, for each cell / position /
  row, depends only on a standard-length window of standard-bounded values. These transfer by
  absoluteness, after the cyclic index arithmetic of §7 has been proved internally.
- **(b) GLOBAL:** induction or iteration over nonstandard ranges (cells, positions, time),
  cyclic word/carry identities over the whole length `n`, population counts of big numbers,
  and existence of least elements. These must be re-proved internally.

---

## 1. The chain at a glance

```
internal Equations / current_radix / first_indices / power      (already internal)
  │  Stage A: arithmetic window (§3)           — mostly (b)
  ▼
Window interface (§4): N, W, c, κ, d with properties (W1)–(W7)
  │  Stage B: cell decoding (§5)               — mostly (a), plus two (b) pieces
  ▼
MarkedWord N s a   (a : Z/N → [0,942), s = ⌊⌊W/47⌋/2011⌋)
  │  Stage C: Wang soundness (§6)              — table facts (a), row induction (b)
  ▼
∃ t < N, (machine.run t).state = none
```

**Important fact (checked by grep).** The cell layer (`CurrentOccupation2011`,
`CurrentTileColors2011`, `CurrentWholeField2011`, `CurrentDecodedWindow2011`,
`CurrentOneHot2011`, `CurrentAdjacency2011`, `CurrentMarkedWindow2011`) uses only seven fields of
`CurrentPolynomialWindow2011.Facts` (`CurrentPolynomialWindow2011.lean:27`): `boolean`, `support`,
`origin`, `carry_bound`, `carry_recurrence`, `carry_equation`, `mask_tests`, plus the number
`W = rank − 47·N·2011`. The 31-coordinate source `x`, `transport`, `C_word`, `F_word`,
`rank_population` and so on are used only to produce these seven. An internal proof can therefore
bypass the external `Carrier66`/31-coordinate source system entirely and target the interface of §4
directly.

---

## 2. Fixed constants

All of these are standard. Line references are definitions.

| Name | Value / definition | Where |
|---|---|---|
| radix `ρ` | `2^47` | `CurrentMaskData2011.lean:12` |
| width `d` | `47·2011 = 94517` | `:14` |
| `β` (port 0) | `ρ^2011 − 1 = 2^94517 − 1` | `:16` |
| `S = lowSupport` | `[0,951) ∪ [960,986) ∪ {1004}`, `|S| = 978`, `S ⊆ [0,2011)` | `:18`; card `CurrentMasks2011.lean:30` |
| `MC = lowPort` (port 2) | `ρ^2011 − 1 − Σ_{j∈S} ρ^j`: radix digit `j` is `ρ−2` if `j∈S`, else `ρ−1` | `:20`, `LowMaskData.lean:10` |
| `highPort` | `ofDigits_ρ(highDigits)` (2011 digits) | `CurrentMaskData2011.lean:23-29` |
| `MF` (port 3) | `highPort + β` (shifted exactly once) | `:31` |
| `K` (port 1) | `rawWord ρ = Σ_{t∈Term} coeff_t · ρ^{exp_t}` | `CurrentKernelData2011.lean:40-42` |

**High-mask cell digits** (`CurrentHighDigits2011.lean:45`, `cellDigit_formula`), for a sub-position `j ∈ [0,2011)`:

- `j=0`: 4 (bit 2)
- `1..916`: 8 (bit 3; the padding tests)
- `917..959`: 0
- `960..968`: 1 (bit 0; South→North copy tests)
- `969..986`: 0
- `987..994`: 1 (East/West copy tests)
- `995..1003`: 0
- `1004`: 1 (marker)
- `1005`: `2^45 − 4` (bits 2..44; the clause)
- `1006..2010`: 0

The global mask digit is `m_k = cellDigit(k mod 2011) − [k = 0]` (`:94`), so the origin digit is 3.
Then `word_ρ(m) = highPort·J − 1` (`:107`).

**Mask constants used in the population argument** (`CurrentMasks2011.lean`):
`σ(lowPort) = 94517 − 978 = 93539` (`:60`), `σ(highPort) = 978` (`:65`), sum `= 94517` (`:78`),
`lowPort ≡ 2 (mod 4)` (`:150`), `highPort ≡ 4 (mod 8)` (`:156`), `lowPort, highPort < β`.

**Kernel** (`CurrentKernelData2011.lean`). `Entry = Fin 942 ⊕ Fin 8 ⊕ Fin 9 ⊕ Fin 8 ⊕ Fin 9`
has 976 entries; `Term = Fin 3 ⊕ Entry` has 979 terms.

`position(e)`:

- selector `i` → `physicalPosition(i) ∈ [0,942)`
- west `j<8` → `978+j`
- north `j<9` → `960+j`
- east `j<8` → `969+j`
- south `j<9` → `942+j`

`weight(e)`:

- selector `i` → `selectorWeight(tile i) = 1 + 2^10·(1 + W + 2^8·N + 2^17·E + 2^25·S)`, where W, N, E, S are the tile's colours (`WangTiles942TableData.lean:67`)
- west → `2^{10+j}`
- north → `2^{18+j}`
- east → `2^{27+j}`
- south → `2^{35+j}`

Terms:

- three bare terms with exponents 18, 1004, 2020 and coefficient 1
- reflected terms with exponent `1005 − position(e)` and coefficient `2·weight(e)`

So `K = ρ^18 + ρ^1004 + ρ^2020 + Σ_e 2·weight(e)·ρ^{1005−position(e)}` (`CurrentKernel2011.lean:82`).

The coefficient mass is `Σ coeff = 7 659 829 036 801 887` (`:446`). Hence
`raw_k ≤ 7 730 197 780 979 551` (`:477`) and `raw_k + 57 < 58·ρ` (`:485`), which is the **carry bound 57**.

**physicalPosition** (`WangTiles942TableData.lean:71`, printed floor-rank formula; bijectivity in
`WangTiles942PhysicalOrder.lean`, data in `WangTiles942PhysicalData.lean:1197`):

- Start (index 0) sits at position 0.
- The other 941 tiles occupy positions `1..941` in strictly decreasing `selectorWeight`.
- Position 1 holds tile 926 (a finish tile). Position 941 holds tile 433 = pass `⟨0,0,0,0⟩`, whose South is 0.
- The initializer, tile 928, is at position 504 (`WangTiles942.lean:165`).

**Cell layout** (sub-positions within one 2011-digit cell `b`, `b ≡ 0 mod 2011`):

- Selectors `c(b+p)`, `p ∈ [0,942)`: physical position `p` ↔ tile `physicalEquiv⁻¹(p)`.
- South label bits `942..950` (9 bits).
- `951..959` empty: excluded from `S` so that bare-2020 sources vanish.
- North `960..968` (9 bits). East `969..976` (8 bits). `977` is in `S` but unused. West `978..985` (8 bits).
- Marker `1004`.
- All label blocks store **complements**: `Σ_j 2^j c(b+942+j) = 511 − South`, North `511 − N`, East `255 − E`, West `255 − W`
  (`CurrentCellLabels2011.lean:283` `labels_of_word`).

**Tile table** (`WangTiles942TableData.lean`, `WangTiles942Data.lean`). `Tile = (west, north, east, south)`.
`headColor(q,b) = 2q+b+2` (`:19`). Indices:

| Index | Tiles |
|---|---|
| 0 | `start = ⟨2,435,3,1⟩` |
| `1..430` | `transitionRow(j)`, `j = 2q+b < 430` |
| `431..434` | pass `⟨0,432a+b,0,432a+b⟩` |
| `435..832` | receive with right rails `6..204` (`|targets true| = 199`) |
| `833..922` | receive with left rails `205..249` (`|targets false| = 45`) |
| `923..926` | finish `⟨0,432a+b,0,438⟩` |
| 927 | initLeft `⟨2,434,2,0⟩` |
| 928 | initHead `⟨3,436,4,4⟩` |
| 929 | initRight `⟨4,436,4,0⟩` |
| `930..932` | reset `⟨1,438,1,p⟩`, `p ∈ {434,435,436}` |
| `933..941` | seam `⟨a²,437,b,437⟩`, `a,b<3` |

The two parameterised families:

- **Transition row** `j`, with action `(w,d,q') = action(j)`:
  `⟨(1−d)·rail(false,q'), headColor(j/2, j%2), d·rail(true,q'), w⟩`.
- **Receive**: `⟨d·rail(d,q), b, (1−d)·rail(d,q), headColor(q,b)⟩`.

Here `rail(d,q) = 205 − 199·d + |targets(d) ∩ [0,q)|` (`WangTiles942Data.lean:348,514`).

Colour vocabulary:

- **Vertical:** 0/1 plain bits; `2..433` head colours (`q ≤ 215`, where 215 means halt); 434/435/436 initializer norths; 437 seam; 438 finish/reset.
- **Horizontal:** 0 none; 1 reset; 2/3/4 initializer; seam west `∈ {0,1,4}`, seam east `∈ {0,1,2}`; rails `6..249`.

**Machine** (`DecimalMachine215.lean:83-88`): `transition q b = act(action(2q + [b]))`. Each action is a
triple (write, moveRight, target), and target 215 means halt. All 430 actions are checked against
the cache (`WangTiles942Data.lean:210 action_eq_decoder`). The first action is `(true,true,1)`, so
`run 1 = ⟨state 1, head 1, tape {0}⟩` (`DecimalMachineInitialization.lean:35,48`).

---

## 3. Stage A — from the internal endpoints to the window

Work in `V ⊨ IΣ1`. Let `v : Fin 14 → V` be a positive zero.

`ArithmeticCarrierSoundness2011.current_natural_equations` (`:452`) gives `Equations β K MC MF v`
(`:121`), with `MF = highPort+β`, for the shifted `u_j = v_j + 1`. Below, write
`J,F,α,z,w = v0,v1,v2,v3,v8`, `q = βJ+1` and `R = ((q−1)(q−F)+α)(q²−1)+(MC+q·MF)J`.

### A1. Radix and power — already internal

`ArithmeticCarrierRadix2011.current_radix` (`:102`) gives, via `ArithmeticPellPowerRecovery.maintained_power`
(`:228`) and `ArithmeticRadixAlignment.factor_alignment` (`:98`), an `L > 0` with:

- `q = 2^{94517·L}`
- `94517·L ≤ R`
- `w = 2^{R − 94517L}`
- `X = wq = 2^R`

**Define** `N := L`, `n := 2011N`, `u := 94517N = 47n`, `W := R − u`.

The external counterparts are `Facts.q_window`, `temporal_power`, `NativeSourceWindow.source_spatial_power`
(`NativeSourceWindow.lean:48`).

### A2. Repunit — (b), easy

`J = Σ_{i<N} 2^{94517 i}`, because `βJ + 1 = 2^{94517N}` with `β = 2^{94517} − 1`
(external `NativeSourceMask.source_J_eq_repunit`, `:69`).

Internally, define the repunit by primitive recursion and prove `(2^d − 1)·rep(N) + 1 = 2^{dN}` by
induction on `N`. Then cancel.

### A3. Gap and transport — ring identities, already internal

`scalar_window` (`ArithmeticPellFirstIndex.lean:268`) gives `C := q − F − α > 0`. Hence
`C + F + α = q`, `F ≤ q − 2`, `0 < F`.

The transport identity `(K + w)·C = F + (z−1)(q−1)` follows by ring algebra from the first
conjunct of `Equations`. External: `NativeSourceWindow.source_transport_identity` (`:18`), `Facts.transport`.

Corollary: `F ≡ (K + 2^W)·C (mod q − 1)`.

### A4. Four-block rank identity — ring identity

```
R = (C−1) + (MC·J + 1) + q·(F + (highPort·J − 1)) + q²·(q−1−(C−1)) + q³·(q−1−F)
```

This uses `βJ = q − 1` exactly once to absorb the `β` in `MF` (`NativeSourceMask.lean:91 packing_four_block`
and `:126 source_rank_four_blocks`). Every block is `< q = 2^u`.

### A5. Mask population — (b) for the repetition, (a) for the constants

```
σ(MC·J + 1) + σ(highPort·J − 1) = u + 2      (NativeMaskPopulation.lean:76)
```

Ingredients:

- (b) `σ(a·rep_d(N)) = N·σ(a)` for `a < 2^d`. This is induction on `N` using
  `ArithmeticBinaryPopulation.concatenate` (`:142`), which is internal.
- (b, easy) `rep ≡ 1 (mod 8)`.
- (a/b) `σ(m+1) = σ(m)+1` for even `m`, and `σ(m−1) = σ(m)+1` for `m ≡ 4 (mod 8)`
  (`population_binary` / `population_div_mod`, internal).
- (a) The constants `σ(lowPort) + σ(highPort) = 94517`, `lowPort` even, `highPort ≡ 4 mod 8`.
  These are standard-parameter facts. Note that `lowPort` and `highPort` are 94517-bit standard
  numbers, so prove them structurally: digitwise `σ` over the 2011 radix digits (`population_ofDigits`).
  Do not evaluate them.

### A6. Population lower bound `σ(R) ≥ 3u + 2` — (b), **NOT yet internal**

External proof: `NativeHalfBinomial.source_half_binomial` (`:110`), then
`NativePopulationLower.source_population_lower` (`:13`).

1. The half index gives `R = 2r+1`.
2. A real-valued Pell ratio estimate gives `2Y = binom(2r,r) + w'·X` with `X = 2^R`.
3. Then `2^{3u+1} | 2Y − w'X = binom(2r,r)`, because `q³ | Y` and `X = 2^R`.
4. Kummer (`lemma_2_15`) gives `σ(r) ≥ 3u+1`, hence `σ(R) = σ(r) + 1 ≥ 3u+2`.

This uses ℝ, `Nat.choose` and the 2-adic valuation. An internal route is proposed in
`Computability/DiophantineConsistency/research/arithmetic-half-binomial-population-proposal.md`
(represented `Pow`, finite binomial expansion, integer rounding). The internal inputs it needs
already exist: `maintained_first_indices` (`ArithmeticPellFirstIndex.lean:371`), which gives
`2n' = R+1`, `k = 2·ycoord n' B`, `c = ycoord R a`, and `maintained_power`.

### A7. Saturation — (b)

`NativeMaskPopulation.native_mask_saturation` (`:27`):

> If `A, F < 2^u`, `R = A + M + 2^u(F+H) + 2^{2u}(2^u−1−A) + 2^{3u}(2^u−1−F)`,
> `σ(M) + σ(H) ≤ u+2` and `σ(R) ≥ 3u+2`, then `A AND M = 0`, `F AND H = 0` and `σ(R) = 3u+2`.

Apply it with `A = C−1`, `M = MC·J+1`, `H = highPort·J − 1`.

It needs:

- subadditivity `σ(x+y) ≤ σx + σy`
- equality iff no carry (`x AND y = 0`)
- block concatenation
- the complement law `σ(2^u−1−A) = u − σ(A)`

The complement law (`ArithmeticBinaryPopulation.complement`, `:165`) and concatenation are internal.
Subadditivity and the no-carry characterisation are proposed in `research/arithmetic-binary-carry-proposal.md`.

### A8. Low-mask decoding of C — (b)

`CurrentSparseDigits2011.decode_low_mask` (`:86`): from `0 < C < ρ^n` and
`(C−1) AND (lowPort·J + 1) = 0` there is a Boolean `c : Z/n → {0,1}` with:

- `C = Σ_k c_k ρ^k`
- `c_0 = 1`
- `c_k = 0` whenever `(k mod 2011) ∉ S`

Reason: the 1-bits of `lowPort·J + 1` are exactly all bit positions except `{47k : k ≠ 0, k mod 2011 ∈ S}`
(`low_mask_word`, `:72`). So `C − 1` is supported there, and `C − 1` even forces `c_0 = 1`.

Internally:

- Define `c_k := fbit(C, 47k)`.
- (b) Lemma: for `a < 2^d`, `fbit(a·rep_d(N), p) = fbit(a, p mod d)` for `p < dN` (induction on `N`).
- (a) The bit pattern of the standard digits `ρ−1`, `ρ−2`.
- (b) A "sparse number = sum of its set bits at multiples of 47" representation, needed for `C = Σ c_k ρ^k`.

### A9. High-mask digits — (b)

`F AND (highPort·J − 1) = 0` and `word(m) = highPort·J − 1` (`CurrentHighDigits2011.lean:107`).
Here `word(x) := Σ_k x_k ρ^k` over `k < n`. With `F = word(d)` (A11), this becomes digitwise
`d_k AND m_k = 0` (`NativeCyclicConvolution.mask_word_iff`, `:157`, for radix `2^t`).

The `−1` borrow lands only in digit 0 (`4 → 3`), so no borrow propagates.

### A10. Kernel and rotation words — (b), the cyclic word identities

Cyclic convolution `conv(a,c)_k = Σ_{i∈Z/n} a_i c_{k−i}` (`NativeCyclicConvolution.lean:27`).
`folded = foldStencil(exponent, coefficient)` (`CurrentKernel2011.lean:453`), so

```
conv(folded, c)_k = c(k−18) + c(k−1004) + c(k−2020) + Σ_e 2·weight(e)·c(k − (1005−position e))
```

with all indices in `Z/n` (`:467 convolution_eq`).

The identities needed modulo `M := ρ^n − 1`:

- `word(folded) ≡ K` (`:458`; from `ρ^n ≡ 1`, `pow_mod_length`, `NativeCyclicConvolution.lean:47`)
- `word(conv(a,c)) ≡ word(a)·word(c)` (`:55`)
- the binary rotation `r := binaryRotation(47, W, c)`, for Boolean `c`, satisfies
  `r_k = 2^{W mod 47} · c(k − ⌊W/47⌋)` (`NativeBooleanRotation.lean:21`)
- `word(r) ≡ 2^W·word(c)` (`NativeCyclicRotation.lean:58`)

Hence `Σ_k raw_k ρ^k ≡ (K + 2^W)·C ≡ F (mod M)`, where `raw_k := conv(folded,c)_k + r_k`.

Internally, `word` over a nonstandard `n` needs a represented iterated sum (PR blueprint, as in
`ArithmeticBinaryPopulation.prefixCount`). Prove `word(rotate e c) ≡ ρ^e·word(c)` once for a
standard shift `e` and once for the nonstandard shift `⌊W/47⌋` (via `div/mod ρ^{n−e}`). Then add up
the 979 standard terms. Alternatively, define everything bitwise from `C` and avoid digit functions.

### A11. Bounded cyclic carries — (b)

`NativeWindowCarry.source_convolution_carries` (`:49`) and `CurrentWindowCarry2011.source_carries`
(`:18`): there are `κ, d : Z/n → ℕ` with:

- (W4) `κ_k ≤ 57`
- `d_k < ρ`
- (W5) `κ_k = ⌊(raw_k + κ_{k−1})/ρ⌋`
- (W6) `raw_k + κ_{k−1} = d_k + ρ·κ_k`
- `word(d) = F`

Inputs: `raw_k + 57 < 58ρ`, and `F ≡ word(raw) (mod M)` with `0 < F < M`.

The external existence proof uses Knaster–Tarski: the least fixed point of a monotone map on
`(Z/n → [0,57])` (`NativeCyclicCarry.lean:37`). **Replace it internally by an explicit end-around carry:**

1. Let `T = Σ raw_k ρ^k` and `E = T div M`. Then `T = F + E·M` and `E < 58`, because `T ≤ 58M − ...`.
2. Put `P_k = E + Σ_{i≤k} raw_i ρ^i`, `κ_k = ⌊P_k/ρ^{k+1}⌋`, `d_k = ⌊P_k/ρ^k⌋ mod ρ`.
3. Then `κ_{n−1} = E` (cyclic consistency, `κ_{−1} := E`). The bound `κ_k ≤ 57` follows by induction on `k`.

`word(d) = F` follows from the decomposition (`NativeCyclicCarryWord.lean:33,63`). The all-`(ρ−1)`
residue is excluded because `F < M`.

The Lean versions of (W5) and (W6) are `Facts.carry_recurrence` and `Facts.carry_equation`.
(W5) is equivalent to (W6) together with `d_k < ρ`.

---

## 4. The window interface — what Stage B consumes

Data: `N ≥ 1`, `n = 2011N`, `W ∈ ℕ`, and `c, κ, d : Z/n → ℕ`. With `raw_k = conv(folded,c)_k + 2^{W mod 47}·c(k − ⌊W/47⌋)`:

| | Property | Lean field |
|---|---|---|
| (W1) | `c_k ≤ 1` | `boolean` |
| (W2) | `c_0 = 1` | `origin` |
| (W3) | `c_k = 0` if `k.val mod 2011 ∉ S` | `support` |
| (W4) | `κ_k ≤ 57` | `carry_bound` |
| (W5) | `κ_k = ⌊(raw_k + κ_{k−1})/ρ⌋` | `carry_recurrence` |
| (W6) | `raw_k + κ_{k−1} = d_k + ρκ_k` | `carry_equation` |
| (W7) | `d_k AND m_k = 0` | `mask_tests` |

Stage B uses nothing else. `W` enters only through `W mod 47` and `⌊W/47⌋ mod n` (and, at the very
end, through `s = ⌊⌊W/47⌋/2011⌋`).

---

## 5. Stage B — cell decoding: (W1)–(W7) ⇒ MarkedWord

A **cell** is `b ∈ Z/n` with `b.val mod 2011 = 0` (`CurrentCellTranslation2011.lean:19`).
Let `t := ⌊W/47⌋` and `φ := W mod 47`.

### B0. Locality lemmas — (a), plus one cyclic identity

**Residue identity** (`CurrentClause2011.lean:27,34`). `(b+e).val ≡ b.val + e (mod 2011)`, and
`((k−e).val + e) ≡ k.val (mod 2011)`, because `2011 | n`.

**Reflected sources stay in the cell** (`CurrentReflectedGeometry2011.lean:134`). For `h ≤ 1004`, the
reflected term at `b+h` reads `c(b + h + position(e) − 1005)` when `h + position(e) ≥ 1005`. Otherwise
the source lies in sub-positions `≥ 1006` of the previous cell, which are outside `S`, so it is 0.
Reflected sums are even (`:66`).

**Bare sources at the test positions** (support kills the others):

| Test position | Bare sources that survive | Bare sources killed by support |
|---|---|---|
| `960+j` (South copy) | `c(k−18) = c(b+942+j)` | `c(k−1004)` → prev `1967+j`; `c(k−2020)` → prev `951+j` (why `951..959 ∉ S`) |
| `987+j` (spatial copy) | `c(k−18) = c(b+969+j)` (East bit); `c(k−2020) = c(prev+978+j)` (West bit of previous cell) | `c(k−1004)` |
| `1004` (marker) | `c(k−1004) = c(b)` | `c(b+986)` (`986 ∉ S`); `c(prev+995)` |
| `1005` (clause) | `c(b+1)` (selector at physical position 1) | the others |

**Carry resets** (`CurrentReflectedGeometry2011.lean:302,320`). If the cell has `selectorCount ≤ 1`,
then for every `h ≤ 1004`, `raw_{b+h} + 57 < ρ`, so `κ_{b+h} = 0`. This uses only (W4)/(W5) and the
budget `CurrentSelectorTail2011.early_reset_numeric` (`:319`). So every carry entering positions
`b+1..b+1004` is 0, **for every bounded solution**. This is per-cell and (a).

### B1. Selector count ≤ 1 in every cell — (a), per cell

`CurrentOneHot2011.literal_count_le_one` (`:44`); `NativePreliminaryCount2011.total_le_one_all_phases` (`:61`).

The clause digit gives
`d_{b+1005} ≡ 2·count + κ_{b+1004} + c(b+1) + 2^φ·ε (mod 2048)`, where `ε ≤ 1`
(`CurrentClause2011.lean:152`). Here the reflected selector weights are `≡ 2 (mod 2048)` and the label
weights `≡ 0` (`:122`). Mask bits 2..44 force the residue to be `≤ 3`.

- **φ ≤ 6 or φ ≥ 11:** this directly gives `count ≤ 1`.
- **φ ∈ 7..10:** first use the 483 padding tests at `b+64..b+546` (mask bit 3), which carry digits
  `≡ 2·prefix_j + unit_j (mod 16)` (`CurrentEarlyPadding2011.lean:292`; carries reset by the selector tail
  mass `137 820 284 543 942`, `CurrentSelectorTail2011.lean:299`). The staircase lemma
  (`PaddingStaircase.prefix_le_three`, `total_le_462`) gives `count ≤ 462`. Then the clause gives `≤ 1`.

All quantities are standard-bounded once `b` is fixed. The staircase is an induction over `j ≤ 483`,
which is a standard bound.

### B2. Fractional phase φ = 0 — (a), at cell 0 only

`CurrentPhaseParity2011.fractional_phase_zero` (`:144`). The marker digit `d_{1004}` has mask 1, so it is
even. Its value is `≡ c(0) + 2^φ·c(1004−t) (mod 2)`, because the reflected sum is even and the
incoming carry is 0 by B0 + B1. Since `c(0) = 1`, `φ ≥ 1` would make the digit odd. So
`φ = 0` and `r_k = c(k − t)`.

### B3. Cell decoding — (a), per cell

`CurrentCellLabels2011.decode_cell` (`:214`), `DoubledClause2011` (`:47-111`). At φ = 0 the clause is

```
d_{b+1005} + ρ·κ_{b+1005} = raw(n,L,u,k,t,β) := 2n + 2048·((2^34 − u)·n + L) + k + t + β
```

where:

- `n` is the selector count
- `L` is `copiedWord(b) = W_bits + 2^8·N_bits + 2^17·E_bits + 2^25·S_bits < 2^34`
- `u = complementedTile(i) = 2^34 − 1 − packed(tile i)` for the selected `i`
- `k = κ_{b+1004}`, `t = c(b+1005−t)`, `β = c(b+1)`

Since `raw < ρ` and the mask `2^45−4` is equivalent to `raw mod 2^45 ≤ 3`:

- **empty cell:** `n=0`, `L=0`, `k+t+β ≤ 3`
- **occupied cell:** `n=1`, `L = u`, so the four label blocks equal the complements of the selected
  tile's colours (`labels_of_word`, `:283`)

Also `κ_{b+1005} = 0`.

**CellDecoded** (`:182`) records this dichotomy.

### B4. Start is selected at cell 0 — (a)

`c(0) = 1` is the selector at physical position 0, which is tile 0 = Start. One-hotness then gives
`Selected(selectorValue c 0, 0)` (`CurrentOccupation2011.lean:75`). Start has South 1, so the
complemented South word is 510, and in particular `c(943) = c(944) = 1`
(`CurrentWholeField2011.lean:45`).

### B5. Copy and marker equalities before whole-field alignment — (a), per cell

`CurrentCopyParity2011.copy_marker_equalities` (`:181`). For every cell `b` and `j < 9`, the digit at
`b+960+j` has mask bit 0 and zero incoming carry. Its parity is
`c(b+942+j) + c(b+960+j−t)`, so

```
c(b+942+j) = c(b+960+j−t)        and similarly        c(b) = c(b+1004−t)
```

### B6. Whole-field alignment `t ≡ 0 (mod 2011)` — mixed

`CurrentWholeField2011.facts_whole_field` (`:73`). Let `r = t mod 2011`. From cell 0:

- the marker gives `c(1004−t) = 1`
- the South copy gives `c(961−t) = c(962−t) = 1`

**(a) Coarse split** (`CurrentFieldOffsets2011.coarse_offset`, `:131`). `1004−t` must lie in `S`, so
`r ≤ 1004` and (`r = 0` or `r ≥ 19`). Then `961−t ∈ S` gives `r ≤ 961`. If `21 ≤ r ≤ 961`, then
`961−r` and `962−r` are two selector positions in the same cell, which contradicts B1. So
`r ∈ {0, 19, 20}`.

Let `S(b) := Σ_j 2^j c(b+942+j)` be the South word of cell `b`, and let `θ(b) = b − (t − r)`, a whole-cell
translation (`theta`, `CurrentCellTranslation2011.lean:54`).

**r = 20 — (a), two cells** (`NativeFieldCycles2011.offset20_excludes_510`, `:100`). We have
`S(b) = 4·S(θb) mod 512 + c(θb+940) + 2c(θb+941)`, where the error is `≤ 2` by one-hotness
(`CurrentSouthShift2011.lean:116,150`). This forces `S(b) mod 4 ∈ {0,1,2}` and `S(b) ≠ 510`, which
contradicts cell 0.

**r = 19 — (b), GLOBAL** (`NativeFieldCycles2011.offset19_excludes_510`, `:68`). We have
`S(b) = 2·S(θb) mod 512 + ε(θb)`, where `ε(b') = c(b'+941)` is the selector of the tile at physical
position 941 (`CurrentSouthShift2011.lean:92`). When `ε(b') = 1`, cell `b'` holds tile 433 and
`S(b') = 511` (`CurrentDecodedWindow2011.facts_terminal_south`, `:49`). The argument:

1. Three predecessors of 510 force `ε = 1` twice, hence the gate value is 511.
2. Then **every iterate along the θ-orbit has even S**: induction on the iterate count, with the
   `successor_mod_four` step.
3. The orbit returns to the start, where `S = 510 ≡ 2 (mod 4)`, a contradiction.

Lean uses `Function.periodicPts` on a `Finite` type. **Internally**, θ is translation by a fixed
element, so `θ^N = id` (equivalently `θ^n = id`). Run the induction on `m ≤ N` for "`S(θ^m b)` is
even"; this is Δ0 in the coded `c`.

Conclusion: `t mod 2011 = 0`, i.e. `W ≡ 0 (mod 47·2011)` (`facts_cell_aligned`, `:131`).

### B7. Adjacency copies after alignment — (a), per cell

`CurrentAdjacency2011.facts_adjacency` (`:195`). With `t ≡ 0 (mod 2011)`, `temporalCell(b) := b − t` is a
cell (`:29,38`), and the temporal digit at `987+j` is 0 because its source sub-position `987+j ∉ S` (`:98`).

The spatial copy (mask bit 0 at `987+j`) gives `c(b+969+j) = c(previousCell(b)+978+j)`, where
`previousCell b = b − 2011` (`:27`). B5 becomes `c(b+942+j) = c(temporalCell(b)+960+j)`.

Combined with B3 labels (`CurrentTileColors2011.lean:43,62`), if `i` is selected at `b` and `j'` at the
other cell:

- **horizontal:** `East(tile i) = West(tile j')` for `j'` at `previousCell b`
- **temporal:** `South(tile i) = North(tile j')` for `j'` at `temporalCell b`

(Complements of equal bit words are equal; the colour bounds are table facts.)

**Temporal shift nonzero** (`CurrentTileColors2011.lean:88`, (a)): `t ≢ 0 (mod n)`. Otherwise Start's
South 1 would equal its own North 435. Downstream this is only cosmetic, since MarkedWord does not
need `s ≢ 0`.

### B8. Occupation of every cell — (b), GLOBAL induction along cells

`CurrentOccupation2011.facts_occupied` (`:111`), `CurrentCellCycle2011.propagate` (`:113`).

Base case: cell 0 is occupied (B4).

Step (a, two cells): suppose cell `b` is occupied by tile `i`. Its West complement is
`255 − West(i) > 0`, because all horizontal colours are `< 250` (`WangTiles942Language.lean:293`).
The East word of `next(b) = b+2011` equals that West word (B7). The empty case of B3 would force the
East word to be 0, so `next(b)` is occupied.

Propagation: every cell is `next^j(0)` with `j = b.val/2011 < N` (`reachable_from_zero`, `:87`).

**Internally:** induction on `j < N` of "cell `2011j` has exactly one selector", which is Δ0 in the coded `c`.

### B9. Coordinates and the tile word — (b), but elementary

`coordinate : Cell → Z/N`, `b ↦ b.val/2011` (`CurrentCellCycle2011.lean:157`), with inverse
`j ↦ 2011j` (`CurrentCellCoordinate2011.lean:37`). The identities used:

- `(a·2011 = b·2011 in Z/n) ↔ (a ≡ b mod N)` (`:47`)
- `coordinate(b − 2011s) = coordinate(b) − s` (`:85,134`)
- `coordinate(0) = 0`

The assignment is `a(j) :=` the unique `i < 942` with `c(2011·j + physicalPosition(i)) = 1`
(`CurrentMarkedWindow2011.lean:38`). Lean uses `Classical.choose`; internally it is a Δ0-definable
function, unique by B8.

### B10. MarkedWord — assembly

`CurrentMarkedWindow2011.facts_marked_word` (`:97`). With `s := ⌊t/2011⌋ = ⌊⌊W/47⌋/2011⌋`
(`stride`, `:30`; natural, unreduced):

- `a(0) = 0` (B4)
- `East(tile a(j)) = West(tile a(j−1))` (B7 + B9)
- `South(tile a(j)) = North(tile a(j−s))` (B7 + B9, using `temporal_coordinate_base`, `:60`)

`MarkedWord` is defined at `WangTiles942Periodic.lean:23`.

---

## 6. Stage C — Wang soundness: MarkedWord ⇒ halt before N

### C0. Finite language facts — all (a), statements about the standard 942-tile table

`Allowed` (`WangTiles942Language.lean:126`) consists of ten families. Allowed is equivalent to
"is `tile i` for some `i < 942`" (`:244 allowed_iff_tile`). Lemmas used:

- `rail(d,·)` is injective on `targets(d)`. Right rails lie in `[6,205)`, left rails in `[205,250)`, and they are disjoint (`:84-115`).
- `small_horizontal_cases` (`WangTiles942InitialHorizontal.lean:21`): a horizontal colour in 2..4 means Start, initLeft, initHead, initRight or a seam. Consequences:
  - east 2 ⇔ initLeft or seam`⟨a²,437,2,437⟩`
  - west 3 ⇔ initHead
  - west 4 ⇔ initRight or seam`⟨4,437,b,437⟩`
- Vertical colours (`WangTiles942Boundary.lean:124-141`):
  - north 437 ⇔ seam ⇔ south 437
  - north 438 ⇔ reset
  - south 438 ⇔ finish
- Inputs (`WangTiles942InputLanguage.lean:50,113`):
  - north = `headColor(q,b)` with `q < 215` ⇔ tile = `transitionRow(2q+b)`
  - north = `b ∈ {0,1}` ⇒ pass, finish, or receive`(d,q∈targets d,b)`
- `ResetHorizontal`: west/east 1 and non-seam ⇒ reset.
- Signals (`WangTiles942Signals.lean:62,74,90,121`):
  - two plain-input neighbours have a zero shared edge
  - a right (left) transition forces the exact receive tile on its right (left) neighbour, with South `headColor(q', b')`
  - plain + zero edges + south ≠ 438 ⇒ pass
- Transition tiles carry the decoded actions (430 checks, `WangTiles942Core.lean:22`).

### C1. Plane pullback — (b), elementary Z/N arithmetic

`address(x,t) = (−x − s·t) mod N` and `plane(x,t) = tile(a(address(x,t)))` (`WangTiles942Periodic.lean:29,32`).

| Identity | Consequence |
|---|---|
| `address(x+1,t) = address(x,t) − 1` | `plane(x+1,t).west = plane(x,t).east` |
| `address(x,t+1) = address(x,t) − s` | `plane(x,t+1).north = plane(x,t).south` |
| `address(x+N,t) = address(x,t+N) = address(x,t)` | horizontal and vertical periods `N` |
| `address(0,0) = 0` | `plane(0,0) = start` |

Internally, only the window `x ∈ [−N−1, N+2]`, `t ∈ [0,N]` is ever needed.

### C2. Initial strip in row 0 — (b): least-number principle + (a) table facts

`WangTiles942InitialStrip.periodic_initial_strip` (`:123`).

1. Start's east 3 ⇒ `plane(1,0) = initHead` (west 3).
2. Left wall: let `L ≥ 1` be the least `j` with `plane(−j,0) ≠ initLeft`. It exists with `L ≤ N`, since `plane(−N,0) = start`. The tile there has east 2 and is not initLeft, so it is a seam with east 2.
3. Right wall: let `R ≥ 2` be the least `j ≥ 2` with `plane(j,0) ≠ initRight`. It exists with `R ≤ N+1`, since `plane(N+1,0) = initHead`. The tile there has west 4, so it is a seam with west 4.

This gives `InitialStrip` (`:23`). Row 0 tiles: `x<0` initLeft (south 0), `x=0` Start (south 1),
`x=1` initHead (south 4 = `headColor(1,0)`), `2 ≤ x < R` initRight (south 0)
(`WangTiles942StripGeometry.lean:22,52`).

Internally: Δ0 least-number principle with parameters `a, N, s`.

### C3. Persistent walls and seam-free interior — (b): induction on time

`WangTiles942StripGeometry.persistent_of_initial` (`:69`), `WangTiles942SeamColumns.seam_iff_zero` (`:42`).
"north = 437" is invariant along a column. It passes from row `t` to `t+1` via time matching plus the
table fact north 437 ⇔ south 437; Lean uses `Int.induction_on`.

So columns `−L` and `R` are seams at every time, and every interior column `−L < x < R` is never a seam,
because its row-0 tile is not a seam. Internally, induction on `t ≤ N` (forward only) suffices.

### C4. Row encoding

`RowEncodes(T, l, r, t, cfg)` (`WangTiles942RowEncoding.lean:23`) holds iff:

- `l < head(cfg) < r`, and
- for all `l < x < r`: `T(x,t).north = color(cfg, x)`

where `color(cfg,x) = headColor(state, tape(x))` if `x = head` and `tape(x) ∈ {0,1}` otherwise
(`WangMachineEncoding.lean:88`). Here halt counts as state 215, so `color ≤ 433` (`:105`).

Initialization (`WangTiles942RowEncoding.lean:66`): `RowEncodes(plane, −L, R, 1, run 1)`, because row 1's
north is row 0's south = `1@0, 4@1, 0` elsewhere, which is `color(initialized)`. This is a finite check.

### C5. One row step — (a) local tile facts + (b) an interval induction for no-finish

`WangTiles942RowStep.row_step` (`:191`). Hypotheses: `Allowed` everywhere, both matchings,
`PersistentStrip`, `RowEncodes` at row `t` for `cfg`, and `cfg.state = some q`. Conclusion:
`RowEncodes` at row `t+1` for `step(cfg)`. The proof partitions interior `x` into three cases.

- **Old head `x = h`** (`HeadBounds.head_transition`). north = `headColor(q,b)` ⇒ the tile is `transitionRow(2q+b)`, so south = the written bit.
- **Moved head `x = h±1`** (`receiver_south`, `:126`). Its north is plain. Its edge matches the transition's active rail. By rail injectivity it is the receive tile, with south `headColor(q', tape(x))`; this includes `q' = 215` (halt).
- **Every other `x`** (`far_pass`, `:107`).
  - West edge 0: the left neighbour is the left wall (east ≤ 2 < 6), a plain cell (pair lemma), or the old head with an inactive side.
  - East edge 0: symmetrically, with the right wall's west ≤ 4.
  - Therefore the tile is pass or finish.
  - Finish is excluded by `no_south438` (`WangTiles942OperatingRow.lean:43`): a south 438 anywhere inside forces reset at row `t+1` there. Reset tiles propagate horizontally through the seam-free interior (`ResetRows.interval_propagate` / `strip_finish_and_reset_of_south438`, `WangTiles942ResetRows.lean:43,132`; this is **(b): induction over positions in `(−L,R)`**). Pulling back gives south 438 at the head, but the transition's south is ≤ 1.
  - So the tile is pass, with south = north = `tape(x)`.
- **New head stays inside the strip** (`next_head_inside`, `WangTiles942HeadBounds.lean:110`). The active rail is ≥ 6, but the wall colours facing inward are ≤ 2 and ≤ 4.

### C6. Main induction and contradiction — (b)

`WangTiles942Soundness.marked_halts_before_period` (`:24`). Suppose `run(t)` is live for all `t < N`.

1. Induction on `k` with `k+1 ≤ N`: `RowEncodes(plane, −L, R, k+1, run(k+1))`. The base case is C4, the step is C5.
2. At `k+1 = N`: `x = 0` is interior (`L ≥ 1`, `R ≥ 2`), so `plane(0,N).north ≤ 433`.
3. But `plane(0,N) = plane(0,0) = start`, whose north is 435. Contradiction.

Hence `∃ t < N, run(t).state = none`. That is `BlankHalts` (`:64`).

Internally:

- The run up to `N` is one coded sequence of configurations. Totality comes from Σ1 primitive recursion in IΣ1; tapes are finite sets with positions in `[−N−1, N+1]`.
- `RowEncodes` is Δ0 in the codes of `a` and the run, and in `L, R, s, N`.
- The case split "∃ t < N halted, or all live" is bounded.

---

## 7. Cyclic indexing: where `Z/n` and `Z/N` occur and the identities that matter

| # | Identity | Used in | Where (Lean) |
|---|---|---|---|
| 1 | `2011 | n` ⇒ `(b±e).val ≡ b.val ± e (mod 2011)`; cell bases closed under `±2011`, `±(t − t mod 2011)`, and `−t` once `2011 | t` | everywhere in Stage B | `CurrentClause2011.lean:27,34`; `CurrentCellTranslation2011.lean:43-120`; `CurrentAdjacency2011.lean:32-53` |
| 2 | `ρ^n ≡ 1 (mod ρ^n−1)` ⇒ `ρ^e ≡ ρ^{e mod n}` | A10 | `NativeCyclicConvolution.lean:39,47` |
| 3 | `word(conv(a,c)) ≡ word(a)·word(c)`; `word(foldStencil) ≡ Σ a_i ρ^{e_i}` | A10 | `:55,222` |
| 4 | `word(rotate_e c) ≡ ρ^e word(c)`; `word(binaryRotation(v,W,c)) ≡ 2^W word(c)`; for Boolean `c`: `binaryRotation = 2^{W mod v}·c(· − ⌊W/v⌋)` | A10, B2 | `NativeCyclicRotation.lean:18,58`; `NativeBooleanRotation.lean:21` |
| 5 | `word(k(·−1)) ≡ ρ·word(k)`, so the local carry decomposition implies `word(raw) ≡ word(d)` | A11 | `NativeCyclicCarryWord.lean:23,33` |
| 6 | `Cell ≃ Z/N` via `b ↦ b.val/2011`; `a·2011 ≡ b·2011 (mod n) ⇔ a ≡ b (mod N)`; `next^N = id`, `next^j(0) = 2011j`; `θ_t` = translation by `−(t − t mod 2011)`, a bijection with `θ^N = id` | B6 (r=19), B8, B9 | `CurrentCellCycle2011.lean:27,70-125,157`; `CurrentCellCoordinate2011.lean:47-146` |
| 7 | Marked word on `Z/N` pulled back by `address(x,t) = −x − s t`; shifts by `(1,0)` and `(0,1)` are `−1` and `−s`; periods `(N,0)`, `(0,N)` | C1 | `WangTiles942Periodic.lean:29-65` |

`s` is used as an element of ℤ, not reduced, and need not be coprime to `N`.

---

## 8. Summary classification and internalisation checklist

| Step | Content | Class | Internal status |
|---|---|---|---|
| A1 | `q = 2^{94517N}`, `w = 2^W`, `X = 2^R` | (b) | **done** (`current_radix`) |
| A2 | `J` = repunit | (b) | easy |
| A3 | `C > 0`, transport | ring | **done** (`scalar_window`) + ring |
| A4 | four-block rank | ring | easy |
| A5 | `σ(MCJ+1) + σ(highPort·J−1) = u+2` | (b) + (a) constants | concatenation **done**; repetition lemma needed |
| A6 | `σ(R) ≥ 3u+2` (half-binomial) | (b), analytic | **open**; proposal exists |
| A7 | saturation ⇒ the two ANDs vanish | (b) | complement **done**; subadditivity/no-carry proposed |
| A8 | `C` ⇒ Boolean `c`, origin, support | (b) bit lemmas | needed |
| A9 | `F AND m = 0` digitwise | (b) | needed |
| A10 | `word(raw) ≡ F (mod ρ^n−1)` | (b) | needed: represented Σ, rotation lemmas |
| A11 | carries `≤ 57`, digits | (b) | needed: explicit end-around carry |
| B0–B5, B7 | per-cell decoding, count, phase, labels, copies, Start | (a) | transfer by Σ0 absoluteness |
| B6 | `t ≡ 0 (mod 2011)` | (a) + (b) orbit for r=19 | orbit induction via `θ^N = id` |
| B8 | all cells occupied | (b) | induction on `j < N` |
| B9–B10 | coordinates, Δ0 assignment, MarkedWord | (b), elementary | easy |
| C0 | tile-language classification | (a) | absolute (standard table) |
| C1 | plane / address | (b), elementary | easy |
| C2 | initial strip via least `L`, `R` | (b) LNP + (a) | Δ0-LNP |
| C3 | seam walls persistent | (b) | induction on `t ≤ N` |
| C4 | `RowEncodes` row 1 = `run 1` | (a) | absolute |
| C5 | row step | (a) local + (b) reset propagation | interval induction |
| C6 | rows `1..N`, contradiction at `(0,N)` | (b) | Σ1-coded run, induction on `k < N` |

### Replacements of non-internal Lean devices

| Lean device | Where | Internal replacement |
|---|---|---|
| `OrderHom.lfp` carries | A11 | explicit end-around formula |
| ℝ Pell ratio | A6 | integer perturbation proof (proposal) |
| `Function.periodicPts` | B6 | `θ^N = id` |
| `Classical.choose` | B9 | Δ0 unique index |
| `Nat.find` | C2 | Δ0 least-number principle |
| `ZMod n → ℕ` functions | everywhere | coded sequences of length `n` |
| `ℤ`-indexed planes | C | finite windows `[−N−1, N+2] × [0, N]` |
| `decide +kernel` table facts | C0 etc. | transfer via `shigmaZero_absolute`, or prove symbolically |
