# iPRA endpoints for package 172's ten-positive 82/240 free-plain circuit

Package 172 (`con-zfc-diophantine-forms/172-pooled-powers-round21`) supplies
the ten-positive circuit
`part2/ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/positive10/positive10_degree240_ops82.json`
(mode `free_plain`, 82 operations, exact degree 240, weight `L = bV`; proof:
`PROOF.md` in the same folder, §1–§6). In the notation of that proof, with
`h = β J`, `q = h + 1`, `C = q - F - α`, `k = η + ζ`:

* `Wbase = q w`, `X = q² w`, `λ = q`: the Pell base is `A = q s (X + 1) + 1`
  and the first parameter `v = X (q s)²`;
* the strip is free: `c = k s + η` (`Y = s`);
* `D = q⁷` and the offset `e - q⁴ s` with `e = k - R - 1`;
* `B = (K0 + q w) C - F`, `V = f (c T - R) - c`, `L = b V`,
  `Z = h D [H (n - L B) + K] - H [D B + h (e - q⁴ s)]`, `M = h D H`.

The `coefficient_binding` equals the 75/402 graph's in every port field
(only the relative `path` differs): the direct-BFS943 tuple, K0 raw
`0a86821a…`, MC `6007cabd…`, MF `48333b0d…`, β `0664a868…`.

The Lean endpoints are in `Lean/DiophantineConsistency/BFS943/IPRATrace82.lean`
(namespace `DiophantineConsistency.IPRATrace82`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, at the
same ports `fixedPorts` as `IPRATrace75`. Each depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## Why not a zero map to 75

In every q-chart the 75 registers use one `Y` in both `c = k Y + η` and
`A - 1 = Y (X + 1)`. An 82 zero has `A - 1 = (q s)(X + 1)` but `c = k s + η`;
a 75 zero with the same `A` has the same `c = ψ_A(R)` and the same `k`
(`v` agrees), and would need `c/k` in `(q s, q s + 1)` instead of
`(s, s + 1)`. So soundness goes through the zero-free boundary of
`research/bfs943-fixed-source-entry` instead.

## Route

**Registers.** `TenPositiveTrace82.regs` is `regsAtC p v X Y W c` (the
`TenPositiveTrace79.regsAt` body with `c` as a parameter; `regsAt_eq` is
`rfl`) at `X = q (q w)`, `Y = q s`, `W = q w`, `c = k s + η`, with `D`, `Z`, `M`
replaced by a structure update. The register `Y` is the scaled ordinate
`λ s = q s`, so every register except `c` (and the `c`-dependent ones) is the
80/258 one up to `D`.

**Norm layer** (`Trace82Factors` … `Trace82GraphPower`): mechanical copies of
the chart-q1 modules `Trace80*`. Across them the strip enters only in lines
`c > k s ≥ k` and in the index-one exclusion, which already took the strip
ordinate and the scale separately (`Direct80IndexOne.impossible` with
`s ≤ q s`); the denominator enters in `Trace82Transport` (`q⁷ ∣ N`,
`cancel_one_mod_seventh`) and `Trace82Projection` (seven cancellations of
`H = q (4 s (X+1)) - 1`); the variable height bound is `X^r < 2 (s + 1)`.
Result: `X = 2^R` (`Trace82GraphPower.graph_power`).

**Soundness = FixedSource** (`Trace82Source.source_of_zero`): at
`sourceVal p v = ![J, F, α, 1, 1, q w, 1, 1, 1, 1]`,

* `power`: `X = q (q w) = 2^R`;
* `mask`, `transport` (`Trace82Integral`): `e = 4 X Y² σ = q⁴ s u`
  (`u = 4 w s σ`) and `q⁷ ∣ e - q⁴ s` give `q³ ∣ s (u - 1)`; `q ∣ 2^R` is a
  power of two, so `u + q³ - 1` is odd and `Trace80Parity.pow2_cancel_odd`
  gives `s = q³ s'`; `H ∣ K` (`Trace82Unweighted`, the projection quotient
  at `X = 2^R`) and `q⁷ ∣ N` in the carrier give `h ∣ B`
  (`TenPositiveTransportIntegral.transport_divisor`), and `B ≥ 0` gives
  `(K0 + q w) C = F + h t`;
* `population`: `β + 1 = 2^d` gives `q = 2^{dN}`; the two scaled Pell
  sandwiches (`Trace82Sandwich`, scale `S = q s`, strip ordinate `s`),
  `ScaledPellRounding.extract` at `c = k s + η` and
  `ArithmeticHalfBinomial.population_lower` with `2^{3dN} = q³ ∣ s` give
  `3 dN + 2 ≤ population R`.

Then `FixedSourceHalt.source_halts`.

**Completeness** (`Trace82HaltGraph.halt_zero_of_model_ports`): the halting
packing (`DirectBFSHaltPellSeed.halt_seeds_transport`) gives the canonical
`J, F, α`, `R = 2r + 1` with `R ≡ 3 (mod 4)` and `2 u N < R`, the unscaled
outer seed at `(2^R, s_Y q³)` and the transport at base `2^{R - uN} = q w''`
(`w'' = 2^{R - 2uN}`). `Trace82ReverseData` applies
`TenPositiveScaledReverseStart.scaled_start` at scale `μ = q`: fresh strip
`C = K s + η'` at the base `a = q s (X + 1) - 1`, with the exact offset
`K = R + 1 + 4 P s₁`, `s₁ ≥ 1` (`twice_index_lt_y`), so with `s = q³ s_Y`
the 82 offset is `e - q⁴ s = q⁷ (4 q X s_Y² s₁ - s_Y) ≥ 0`; the auxiliary
seed and the carrier coordinate `n` at the parent weight `(F b₀) u` are as
in `Trace76ReverseData`. `Trace82ParentMap` (the squared-trace parent and the
shift `T ↦ f T - d R`, as `Trace76ParentMap`) and `Trace82ReverseGraph` give
the positive 82 zero `(J, F, α, i, T, w'', s_Y q³, n, η', ζ')`.

`Trace82ModelIff.positive_model_iff` joins both directions; the iPRA
wrappers are those of `IPRATrace75`.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the
82 and 75 JSON graphs, `TenPositiveTrace75.lean` and `Trace79Regs.lean`;
checks the graph metadata, no dead rows, and the port binding (equal to the
75 graph's except `path`, with the four direct-BFS943 raw hashes); checks
that `regsAt` is the parameterized 75 register map and `regsAtC` is `regsAt`
with `c` as a parameter; parses `regsAtC`, the 82 instance and structure
update in `regs`, and `value82`, and compares the output with the JSON output
after exact commutative-ring structural normalization (also `X`, `qY`, `c`,
`D`, `Bt`, `Znum`, `Mtot` individually). It rejects five mutations
(denominator `q⁶`; strip `c = k q s + η`; Pell scale `1`; transport base `w`;
sign of the `q⁴ s` correction), and checks the literal and endpoint
definitions verbatim and that `fixedPorts` is textually the `IPRATrace75`
one, so `reviews/bfs943-source-promotion/tools/check_ports.py` covers 82 too.
Output: `check-output.json`. These are finite external checks, not Lean
theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Trace82Regs` | `regsAtC`, the 82 `regs`, `value82`, register lemmas |
| `Trace82Factors` | natural representatives (`c = k s + η`, `D7 = q⁷`) |
| `Trace82Residue` … `Trace82NormOffset` | norm layer (copies of `Trace80*`) |
| `Trace82Transport` | `B ≥ 0`, mask, `q⁷ ∣ e - q⁴ s`, `q⁴ ∣ e` |
| `Trace82Projection`, `Trace82VariableHeight`, `Trace82GraphPower` | `X = 2^R` |
| `Trace82Unweighted` | `H ∣ K` |
| `Trace82Integral` | `q³ ∣ s`, natural transport `(K0 + q w) C = F + h t` |
| `Trace82Sandwich` | both scaled Pell sandwiches at the free strip |
| `Trace82Source` | positive 82 zero ⇒ `FixedSource` |
| `Trace82ParentMap` | squared-trace parent and its positive shift |
| `Trace82ReverseData` | scaled (`μ = q`) reverse data with the `q⁷` offset |
| `Trace82ReverseGraph` | source data ⇒ positive 82 zero |
| `Trace82HaltGraph` | halting ⇒ positive 82 zero |
| `Trace82Syntax` | literal `TenPositiveTrace82.expression`, `Trace82BFSSyntax.literal_zero_iff` |
| `Trace82ModelIff` | `positive_model_iff` |
| `IPRATrace82` | the iPRA endpoints |
