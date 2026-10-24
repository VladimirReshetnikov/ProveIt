# Research brief: a one-word native window, for nine positive unknowns

Direction chosen by Vladimir on 24 October 2026 (see NEXT_STEPS.md): make
the ten-positive kernel a nine-positive equation by changing the compiler's
window so that the transport reads one tableau word. This brief fixes what
the present window does, why the kernel cannot absorb a third source
unknown, and where a redesign has to act. Nothing here is a result.

## 1. What the present window is

From `NativeSourceWindow.source_native_window` and
`NativeMaskPopulation` (`Computability/DiophantineConsistency/Lean/`), and
the compiler proofs of packages 36 and 44 and
`HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md`:

- q = B^N = 2^(dN), J = 1 + B + … + B^(N−1); a word of N cells of d bits each
  is an integer below q.
- **C** is the tableau word: the whole blank run of K215 as a Wang tiling,
  one cell per base-B digit (selector bits, label copies, anchors).
- **F** is the test word: F ≡ (K_0 + w)·C (mod q−1) with K_0 = D_C + B·D_R
  two fixed convolution kernels and w = X/q = 2^R/q ≡ B^h (mod q−1) a cyclic
  rotation by the temporal stride h. Multiplication modulo B^N − 1 is cyclic
  convolution of the N digits, so F is the convolution of the tableau with
  the machine's local rules plus its own row shift.
- The rank packs both words with their complements:
  R = (C−1 + M_C J + 1) + q (F + M_F J − 1) + q^2 (q−1−(C−1)) + q^3 (q−1−F),
  i.e. R = (q^2 − S)(q^2 − 1) + (M_C + q M_F^src) J with S = qF + C.
- The half-binomial kernel forces σ_2(R) = 3dN + 2 (q^3 | Y with Y = M/2),
  and that population saturates the subadditivity bound only if
  (C−1) AND (M_C J + 1) = 0 and F AND (M_F J − 1) = 0: the two mask tests
  that make the tiling valid (clean bands, anchors, overlaps).
- The decoding needs C−1 < q and F < q as genuine digit fields. The slack
  unknown alpha with C + F + alpha = q witnesses this (and F + C < q holds
  for canonical words).

So the kernel's three source unknowns are J (size), and the two words F and
C. The transport tests the two residues C mod (q−1) and F mod (q−1)
independently (q ≡ 1 makes S ≡ F + C, only their sum), so one unknown
cannot carry both.

## 2. What the kernel can and cannot absorb (checked on paper)

- A quotient x/m of a divisibility is absorbed by the norm's sum variable
  through coprime partial fractions (q^3 | Y, q−1 | B_t, mu^2 | e, H' | K_pos
  today).
- One unbounded-sign quantity is absorbed by a weight: the transport term
  −W·t with W above every other term forces t ≥ 0, because a negative t
  makes the sum variable negative.
- One positivity of a derived quantity is absorbed by making it the scale of
  the roots (the margin finalizer of Jones / package 52): with the roots and
  a positive majorant M_0 multiplied by m, a zero forces m > 0 since the
  bracket M_0 ± roots is positive and the other side is positive. For this
  kernel: unknowns J, F, C, alpha := q − F − C, roots 3 tau and f scaled by
  alpha, y and its centre V unscaled, M_0 = 3 L_0 + 2(K_0 + w) + 2 and a
  positive register Q_0 = 2(K_0 + w) + 2c + X + 2q + cT' on the integer side
  exclude alpha ≤ 0 at unchanged degree 368. This trades alpha for C; it
  does not remove an unknown.
- Two interacting positivities are not absorbed: with F := (K_0 + w)C −
  (q−1)t derived from a quotient unknown t, both F ≥ 1 and alpha ≥ 1 are
  needed, and every weight or scale that excludes a bad case of one lets a
  bad case of the other be compensated (the required majorants dominate
  each other circularly; F + alpha = q − C is the only coupling and it is
  not sign-definite).

Hence, with the devices tried here, nine positive unknowns need a window
with one tested word. As the research session notes in NEXT_STEPS.md,
these are obstacles to the tested changes, not an impossibility proof: a
different arithmetic encoding of the two residues may exist. (The same
session has since lowered the ten-positive kernel to 98 operations and
degree 360 with the index weight L = kI + b, which also corrects the
"degree floor" wording of the first note.)

## 3. Where a redesign could act

1. **Self-consistency instead of a test word.** Encode the run as C and
   require the convolution-plus-shift to reproduce a fixed function of C
   itself, so the transport becomes (K_0 + w − κ)·C ≡ 0 (mod q−1) for a
   fixed κ, with the validity carried by C's own mask. The rank then packs
   C and its complement only (two blocks), and the population target is
   dN + const. The question is whether a local Wang rule set can be written
   so that validity is "F = κ C" rather than "F avoids forbidden bits".
2. **One 2N-digit word.** Take S = qF + C as the single unknown and express
   the transport on S. Digit extraction (C = S mod q) costs a quotient
   witness; this only works if the compiler's transport can be rewritten to
   use S modulo a different modulus whose residue separates the fields
   (e.g. modulo q^2 − 1, where S ≡ F·q + C has both digits).
3. **Move the F-test into the exponent register.** The forbidden-bit test on
   F is a disjointness; if the kernel's K_pos / H' projection could carry a
   second residue class, the test word need not be a rank digit. This
   touches the Pell projection lemmas, not only the window.

Each option needs a new soundness proof of the window (the analogue of
package 44, Sections 5–7, and `NativeSourceWindow`) and new fixed
coefficients. The arithmetic kernel downstream (Pell roots, norm, carrier)
is unchanged and already sits at degree 368 for ten unknowns, so a
successful one-word window gives nine positive unknowns at degree of order
400, against 997,810 today.

## 4. Starting points in the repository

- Window and masks: `Lean/DiophantineConsistency/NativeSourceWindow.lean`,
  `NativeSourceMask.lean`, `MaskPopulation.lean`, `NativeHalfBinomial`;
  notes `NATIVE_SOURCE_WINDOW.md`, `NATIVE_HALF_BINOMIAL.md`,
  `NATIVE_FORMULAS.md`.
- Compiler proofs: `con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md`
  (tile language, coefficient recipe, geometry, rank controller);
  `36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md`;
  `HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md`
  (Sections 4–6: fixed compiler, synchronization, soundness, completeness).
- Tile data: `44-b4-sparse/native/source/coefficients__wang943_tiles.json`
  and the K215 machine `BusyBeaver/Research/ZFC/candidate-k215/k215.tm`.
- The kernel to attach: `candidates/ten-positive-zero-offset/`.
