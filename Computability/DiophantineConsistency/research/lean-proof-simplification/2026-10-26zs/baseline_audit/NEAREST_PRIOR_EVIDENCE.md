# Exact nearest-prior evidence

Full source bytes are included beside this file; hashes bind them to the frozen repository. Source quotations are distinguished from this audit’s decisions.

## EX051_native_rank_casts.txt
[Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26c/notes/arithmetic.txt](https://github.com/VladimirReshetnikov/ProveIt/blob/9d9d1123b39927d30363f1dcd53c23f0575c30ee/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26c/notes/arithmetic.txt); Git blob `feec48382ec712099069831f76e1d15102507d64`.

Lines 227–251:
```text
227: ## 6. Normalize Nat/Int transitions at explicit semantic boundaries
228: 
229: **Targets:** `NativePellFirstIndex.source_first_index_exact:40-92`,
230: `source_first_pair:103-125`, and the source-window family.
231: 
232: Several proofs repeat a local name `R := (nativeRank x).toNat`, a proof
233: `(R : ℤ) = nativeRank x`, and conversions of rank inequalities between
234: natural numbers and integers. Establish these once in a source-facts API
235: whose constructor is proved from the actual positive source rows. Its fields
236: can include nonnegativity, the cast equality, and the lower bounds that are
237: already consequences of the source.
238: 
239: The project already demonstrates this style in
240: `CurrentPolynomialWindow2011.Facts:26-66`: its constructor derives a coherent
241: source, cyclic window, carries, and masks from an actual polynomial zero.
242: Extend this existing pattern where it removes repeated derivations. Keep
243: small theorems taking only the facts they really need; do not force every
244: helper to import the entire current polynomial endpoint.
245: 
246: For natural subtraction, a normalization lemma must retain its ordering
247: premise. In particular, casting `a-b` requires `b≤a`; `ring` is appropriate
248: after that premise is used, not before. Do not replace a natural subtraction
249: by an integer subtraction without proving this bridge. The current
250: `source_eq_of_remainder_le` and `source_eq_wrapped` already handle this
251: correctly; their exact full-modulus semantics should be preserved.
```

## finite_distributivity.tex
[Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/02_local.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/9d9d1123b39927d30363f1dcd53c23f0575c30ee/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/02_local.tex); Git blob `da09ca3faab2a6cf05f59e20bfb352f71e0f8f8e`.

Lines 210–222:
```text
210: \subsection{Smaller opportunities and a reason to keep an existing proof}
211: 
212: The archive contains several further local experiments; they are useful
213: after the higher-value reuse changes, not a mandate to minimize every proof.
214: 
215: \begin{itemize}
216: \item \textbf{Convolution factorization.}
217: In \code{NativeCyclicConvolution.word_convolution}, the final distributivity
218: step at \src{NativeCyclicConvolution.lean}{79}{87} can be expressed using
219: \code{Finset.sum_mul}, \code{Finset.mul_sum}, \code{pow_add}, and controlled
220: associative/commutative simplification. The candidate changes that span from
221: 9 to 3 lines. Preserve the preceding modular-congruence argument; a global
222: \code{ring} call does not replace it.
```

## normalized_growth.tex
[Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26zc/report.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/9d9d1123b39927d30363f1dcd53c23f0575c30ee/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26zc/report.tex); Git blob `00fd62934c0d5cba47236a48fa009fa0a2e43896`.

Lines 345–375:
```text
345: \subsection{The coefficient seventy-two: shift the threshold}
346: 
347: \code{NativeHalfBinomial.seventy_two_mul_lt_two_pow} states
348: \[
349:  r\ge4\quad\Longrightarrow\quad72r<2^{2r+1}.
350: \]
351: Write \(r=4+n\). Then
352: \[
353:  2^{2r+1}=512\cdot4^n.
354: \]
355: Mathlib's \code{Nat.lt_pow_self} gives \(n<4^n\), hence \(n+1\le4^n\).
356: Consequently,
357: \[
358:  72n+288<512n+512\le512\cdot4^n.
359: \]
360: After the power identity is normalized, only a linear arithmetic argument remains:
361: 
362: \begin{LeanCode}
363:   obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
364:   have h : n < 4 ^ n :=
365:     Nat.lt_pow_self (by decide : 1 < 4)
366:   rw [show 2 * (4 + n) + 1 = 9 + 2 * n by omega,
367:     pow_add, pow_mul]
368:   norm_num
369:   omega
370: \end{LeanCode}
371: 
372: Again, this does not strengthen a hypothesis or replace the displayed constants.
373: It proves the exact original statement. In the actual source, each old proof body
374: has eight nonblank lines and each replacement has five. There is no new helper to
375: amortize. The two containing source snapshots decrease by six physical lines.
```

Lines 570–583:
```text
570: \subsection{Can threshold normalization be recognized systematically?}
571: 
572: The two checked scalar examples have a common practical pattern: several exponential
573: terms share a base after normalization, or a lower threshold allows an exponent
574: shift that leaves a standard growth inequality. A future tool could propose these
575: changes, but the final certificate should expose the normalized natural variable,
576: its lower bound, and the resulting polynomial or linear inequality. No new tactic
577: or broad automatic simplifier is implemented here.
578: 
579: For this project, useful candidates would have an existing local scalar induction
580: and a direct downstream consumer. Replacing a readable one-line library theorem by
581: new infrastructure would have no benefit. Earlier generic advice to keep large
582: powers symbolic remains part of the assumed baseline.
583: 
```

## NativeSourceMask.lean
[Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeSourceMask.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/9d9d1123b39927d30363f1dcd53c23f0575c30ee/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeSourceMask.lean); Git blob `0142e54eede2fe34e3bc213f46966eeba80c9d04`.

Lines 87–94:
```text
87: /-- The four-block identity is ordinary integer algebra; the beta-J
88: relation is used exactly once, including the shifted fourth source port. -/
89: theorem packing_four_block {q F C MC MF J beta : ℤ} (h : beta * J = q - 1) :
90:     ((q - 1) * (q - F) + (q - F - C)) * (q ^ 2 - 1) +
91:       (MC + q * (MF + beta)) * J =
92:     (C - 1) + (MC * J + 1) + q * (F + (MF * J - 1)) +
93:       q ^ 2 * (q - C) + q ^ 3 * (q - F - 1) := by
94:   linear_combination q * h
```
