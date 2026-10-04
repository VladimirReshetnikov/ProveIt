# Sharing the six rotated occurrence polynomials in Report 48

A complete emitted component with **7,886 operations = 3,950 M + 3,936 A** replaces the 24 independent occurrence Horner chains in the authenticated Report 48 grammar. The saving is **38,146 operations = 19,066 M + 19,080 A**. Every one of the new computed gates is live, and all 24 output polynomials are independently expanded and compared coefficientwise.

This packet emits the replacement component in full. It specifies a complete grammar splice into Report 48 and derives the resulting whole-source ledgers, but does **not** emit, replay, or hash a new 14.6-million-gate complete source. Its full-source degree, domains, and representation theorem are inherited by polynomial equality. No archived Python is imported or executed; the historical archive is read only as authenticated data.

## 1. Exact baseline and ports

The baseline archive is `docs/incoming/Exact_Fusion_of_the_Ant_Background_Polynomials_Package.zip` at commit `c5612efa171fa62470285049ee45d1d06ee25578`, Git blob `5c17a62cb5519c85608b9c6a50184e2d95347bc4`, SHA-256 `45f8dcf697012fc67cd9155f76980787fef8ff3cb4f4746ef54c4c3375c7bb65`, size 2,162,628 bytes. The checker authenticates that historical blob directly, so subsequent archive relocation or deletion in the working tree does not change its input. Five member pins are also checked:

| Member below `Research_Report48/` | SHA-256 |
|---|---|
| `README.md` | `03a15a36c708e530e3cd644526bbdcc0e2e06370fd2903703f6a3899c9ef6ae4` |
| `science/PROOF.md` | `0a140e526a8c7e7ee5076204e258fdddd431d8c02e49dd9a8eff9a673d195af8` |
| `independent_audit/GENERIC_PROOF.md` | `6bf435b17c1653c6e684df47a191b5cd4343940e361f39f8a59237453763855b` |
| `science/fusion_source.py` | `5e433001dcdb4a26f7dcb0419a41f124fae983aeb76088d55d4b603802232f60` |
| `science/fused-receipt.json` | `8230ba6bed0e6209f814094168551282252c709681cc0b744cace678e4b703ee` |

The source interface is read from `Fusion.corrections`, lines 169–189, and its call from `Fusion.build`. For each kind `a` in DUP, NAND, MOVE_LEFT, MOVE_RIGHT, the already constructed values are `T[a,s]`, for `0 <= s < 957`. The other ports are the already paid `Y=W^600` and the already paid zero expression `1-1`. These 3,830 port bindings are explicitly listed in the new packet; they add no inputs to the complete polynomial, no witnesses, and no new literals.

The old source constructs, for `b=0,1,2` and `phase=0,288000`,

    L[a,b,phase](Y) = sum(s=0..956) T[a,s]
                          Y^((480-b-s-phase/600) mod 960).

It uses an independent full 960-coefficient Horner chain for each of these 24 polynomials. The three absent occurrence positions are filled with the existing zero wire. Each chain costs 959 M + 959 A. The 24 products with the independently built short correction polynomials, and the two eleven-addition phase sums, are separate and remain unchanged.

## 2. Six blocks give all six rotations

Fix a kind. Define the length-960 coefficient array

    A[j] = T[a,(480-j) mod 960] if that index is below 957,
           0 otherwise.

For `r=b+phase/600`, the coefficient of `Y^j` in the required output is `A[(j+r) mod 960]`. The six possible offsets are precisely

    0, 1, 2, 480, 481, 482.

Split A at boundaries `0,1,2,480,481,482,960`. The six block lengths are `1,1,478,1,1,478`. For each block B of length l, compute the ordinary polynomial `P_B(Y)=sum(j=0..l-1) B[j]Y^j`. The four length-one blocks alias their coefficients; the two length-478 blocks are paid Horner chains.

Each requested rotation is a cyclic ordering of these **whole coefficient blocks**, starting at its corresponding boundary. To concatenate a low block B of length l with an already constructed high polynomial Q, compute

    P_B(Y) + Y^l Q(Y).

Process the six blocks from high to low in that order. Exactly five multiplications and five additions produce each rotated polynomial. Only `Y` and `Y^478` occur as shifts; the latter is built once, shared between all four kinds, by the ordinary binary chain.

This is distributivity in the polynomial ring over the independent coefficients. The word “cyclic” describes a finite permutation of the coefficient array, not arithmetic modulo `Y^960-1`. Every final exponent is the ordinary nonnegative exponent prescribed above. No division, inverse, branch, positivity premise, or exception at Y=0 or ±1 occurs. In particular the identity remains true for arbitrary signed coefficients, independently of any ant-dynamics or geometric theorem.

## 3. Literal schedule and exact ledger

The receipt contains all 7,886 rows, all 24 output wires, all 24 block outputs and all 3,830 inherited input bindings. Rows use only multiplication and addition. The binary exponent 478 has nine bits and seven set bits, hence its chain costs `8+6=14` multiplications. The complete ledger is:

| Part | M | A |
|---|---:|---:|
| Shared `Y^478` | 14 | 0 |
| Four kinds × two length-478 blocks | 3,816 | 3,816 |
| Four kinds × six five-step concatenations | 120 | 120 |
| New component | **3,950** | **3,936** |
| Old 24 full length-960 Horners | 23,016 | 23,016 |
| Saved | **19,066** | **19,080** |

The checker reconstructs each register in a sparse polynomial ring with Y and the independent occurrence ports, checks closure and row ordering, and compares each final polynomial with a separately constructed dense exponent formula. That proves all 22,968 nonzero occurrence terms in the 24 outputs exactly. It also checks that the union of the output dependency closures contains every computed row and every declared inherited port. Five numerical base choices provide 120 supplementary output checks; these numerical tests are not the identity proof.

## 4. Full grammar splice and inherited totals

In the pinned `Fusion.corrections`, keep the twelve short `Q[a,b]` Horner outputs. Before the old phase loop's 24 correction products, emit this new component, binding its Y, zero and occurrence ports to the existing wires. In each old `t=self.horner(self.Y,coeffs)` call, alias t to the corresponding saved component output. Keep every following multiplication by `qb[kind,b]` and both phase sums. The new component depends only on wires already available at that point, so the splice is topological.

Each substituted t is the same polynomial for all assignments. Induction preserves the two phase corrections, the fused tile polynomial, both dense-Horner replacement outputs, every later arithmetic register and residual, and the full sum-of-squares finalizer. No change to positive coordinates or to the inherited ordinary/raw input interface occurs. The fact that Report 48 stores a compact generator rather than a flat stream does not change this algebraic substitution theorem; it does limit what was newly replayed here.

The replaced complete stage changes from `23,040 M + 23,038 A = 46,078` to `3,974 M + 3,958 A = 7,932`, including the unchanged products and phase sums. The fused spatial source changes from 92,107 to 53,961 gates. The retained 14,563,366-gate prefix and the other 3,461 / 3,471 main gates are unchanged. The resulting ledgers are therefore:

| Raw interface | M | A | Total | Positive witnesses |
|---|---:|---:|---:|---:|
| Two inputs | 5,952,054 | 8,668,734 | **14,620,788** | 465 |
| One input | 5,952,058 | 8,668,740 | **14,620,798** | 467 |

Both retain one equation and exact variable degree 2,304,000 by equality with the inherited complete polynomial. These are exact ledger consequences of the specified grammar transform, not newly generated complete-stream hashes. The old source hashes must not be assigned to the transformed streams.

Pascal's separate endpoint splice identifies its duplicated `W^576000` with the initializer's already paid G and deletes nine multiplications. That splice affects a later disjoint source cone and composes with this one. If both specified transformations are applied, the totals are 14,620,779 / 14,620,789; the present packet does not emit the endpoint replacement or the combined whole source.

## 5. Replay and limits

With this helper and saved receipt in the same directory, run against a repository containing the pinned historical commit:

    python3 ant48_rotated_occurrence_sharing.py --repo /absolute/repository --expect ant48_rotated_occurrence_sharing.json
    python3 -O ant48_rotated_occurrence_sharing.py --repo /absolute/repository --expect ant48_rotated_occurrence_sharing.json

A new receipt can be written with `--output` to a previously nonexistent file. The checker uses explicit exceptions for its obligations, so optimized Python does not disable checks. Receipt comparison is exact text after canonical generation and a checked JSON round trip; it does not normalize away changed types or source rows.

The component is fully emitted and checked. The upstream multi-million-gate coefficient prefix, literal complete source and simulation/number-theoretic theorems remain inherited. No archive code, old builder, physical ant, or enormous coefficient integer was executed or instantiated. This saving changes neither the ant theorem nor the witness count and supplies no improvement to the current universal 84-operation representation. There is no optimality or lower-bound claim.
