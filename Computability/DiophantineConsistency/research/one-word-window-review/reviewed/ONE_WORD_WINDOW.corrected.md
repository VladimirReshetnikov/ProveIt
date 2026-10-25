# Research brief: a one-word native window, for nine positive unknowns

Direction chosen by Vladimir on 24 October 2026 (see NEXT_STEPS.md): make
the ten-positive kernel a nine-positive equation by changing the compiler's
window so that the transport reads one tableau word. This brief fixes what
the present window does, why the kernel cannot absorb a third source
unknown, and where a redesign has to act. Section 2d records the algebraic
restriction from complement transport. Section 2e proves a stronger obstruction
under the retained mask/population interface and states its remaining scope.

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

## 2a. Three facts that pin the target down

Checked against the window and the compiler proofs after the first draft
of this brief:

1. The test word has to be the reduced residue F = (K_0 + w)·C mod (q−1).
   The rotation factor w = 2^(R − dN) is astronomically large (R is of the
   order of q^3 to q^4), so the unreduced product (K_0 + w)·C has no cell
   structure; the reduction by q − 1 = B^N − 1 is what turns 2^R into a
   rotation by h cells. The quotient t = ((K_0 + w)C − F)/(q−1) is therefore
   unavoidable, and exactly one of F and t has to be a word-sized unknown.
2. J cannot be replaced by a quotient. It multiplies the masks (M_C·J + 1,
   M_F·J − 1) and the index term (M_C + qM_F)J inside R, so it must be an
   integer register; quotients absorbed by the norm's sum variable never
   re-enter other registers.
3. The only bit test available is population saturation: a word whose bits
   are tested must be a digit field of R, together with its complement.
   Hence every window of the present type needs three source unknowns:
   {J, C, F or t}.

Two shortcuts fail for the same reasons. Dropping C's own mask test does
not work: a stray bit of C outside the data positions is moved by the
convolution kernels (shifts by 30, 62, 1100, 2201 and 4393 − e within a
cell) to positions that are not tested, so it stays invisible unless C is
itself a tested field. Avoiding the reduction modulo q − 1 by zero-padding
the top rows does not work either: the temporal stride is the row width,
which the compiler reads only from R modulo dN (the rank controller sets
R ≡ d·width mod dN, so 2^R ≡ B^width mod q − 1), and every linear layout of
a space-time diagram leaves one neighbour offset unbounded, so the stride
is intrinsically a cyclic rotation and some word must carry its residue.

So a one-word window cannot keep "F has no bits at the test positions"
as its validity condition. It must make the tableau word C
**self-certifying**: validity of the tiling has to be a population
identity on C's own digit fields, with the neighbour comparisons (north
against south of the temporal predecessor, east against west of the
spatial neighbour, anchors) folded into C's encoding rather than into a
derived word. Options 1–3 below are judged against this.

## 2b. The historical complement target: alpha = 1 (24 October, evening)

In the current fused ten-positive kernels (packages 113, 116, 119, 121 and
their research-session descendants down to 86 operations) the three source
unknowns are J, F and alpha; the tableau word is derived, C = q − F − alpha,
and the transport quotient t = B/g is already absorbed by the norm. So the
one unknown a nine-positive form must lose is the slack alpha.

Fixing alpha = 1 gives C + F = q − 1 = B^N − 1, i.e. **C is the bitwise
complement of F**. Then:

- the transport (K0 + w)·C ≡ F (mod q − 1) becomes
  (K0 + w + 1)·C ≡ 0 (mod q − 1): the shifted-and-convolved tableau plus the
  tableau itself is a multiple of B^N − 1;
- the two mask tests become tests on C alone: (C − 1) AND (MC·J + 1) = 0 and
  (NOT C) AND (MF·J − 1) = 0, i.e. C has fixed zeros at the MC positions and
  fixed ones at the MF positions;
- the rank keeps its four-block form, with the F-blocks equal to the
  complement blocks of C, so the population target 3dN + 2 is unchanged.

So the self-certifying window of section 2a has a precise arithmetic form:
a tile encoding whose cyclic convolution with the fixed kernels and the row
shift, **plus the word itself**, sums to all ones in every cell (no carries
across cells), exactly when the tiling is valid. The current Wang943 encoding
does not have this property: its test word F is zero at the test positions
and unconstrained elsewhere, while here every bit of F would be forced.
This proposal kept the population target and both masks unchanged. Section2e
now rules out that combination before transport is considered. A different
one-word encoding would need a changed mask/rank interface or another slack
expression; no nine-positive circuit follows from fixing alpha=1 here.

### 2c. First feasibility analysis of the complement form

*Local edge checks are expressible.* With alpha = 1 the identity
(K0 + w + 1)·C ≡ 0 (mod B^N − 1) says that, cell by cell, the bits the fixed
kernels and the row shift deliver to each position, plus the cell's own bit
there, sum to the corresponding digit of a multiple of B^N − 1. Store every
edge colour in two places, once plainly and once complemented
(w̄ = 2^m − 1 − w). If the kernel delivers e_i onto the complemented field
w̄_(i+1) of the east neighbour (and s_i onto n̄_(i+h) through the row shift),
each bit position receives e_bit + w̄_bit, which is 1 exactly when the colours
agree at that bit, and 0 or 2 when they disagree. So matching colours
produce an all-ones field with no carry, which is what the complement form
requires. Tile selection (one of the 943 tiles per occupied cell) is already
a linear aggregate in the present compiler (package 44, section 3, the
aggregate lemma with a = 10, m = 41), so it can be re-targeted at all ones
by fixed ones of C at known positions.

*What must still be excluded.* A residue ≡ 0 (mod B^N − 1) is m·(B^N − 1)
for a small m, not only B^N − 1. For example, "every position receives 2"
(m = 2: all plain and complemented copies equal to 1, i.e. mismatches
everywhere) passes the congruence, and so do balanced patterns of 0's and 2's
whose carries wrap around the cycle. These must be excluded by C's fixed
zeros and ones and by the population target σ2(R) = 3dN + 2, and the
exclusion has to be proved, as the present compiler proves its clean bands
and anchor parities (package 44, section 5;
`HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md`, section 4).

*What a full compiler still needs.* Re-encoding the 943-tile language with
complemented copies (roughly doubling the cell width d), new anchor and
boundary handling for the start and end markers, a new carry analysis for
the cyclic sum, re-derived fixed coefficients (K0, MC, MF) and population
calibration, and a new soundness and completeness proof of the window.
None of this is attempted here; the analysis above only shows that the local
part of the complement form is not obstructed.

### 2d. A global obstruction to the complement form (24 October, later)

The local analysis of 2c is not enough: the global congruence turns the
accepted words into a group.

*The accepted set before masks is cyclic.* Put M = B^N − 1 and
g = gcd(K0 + B^h + 1, M). Since w ≡ B^h (mod M), the complement form
(K0 + w + 1)·C ≡ 0 (mod M) holds exactly for the multiples C = k·(M/g),
0 ≤ k < g. The fixed-bit masks then select a subset of these g words.

*Rows evolve by a fixed multiplier.* k·(M/g) is the N-digit repetend of k/g
in base B: its digits come from the remainders r_(j+1) = B·r_j mod g. One row
later (h cells) the remainder is multiplied by B^h, and B^h ≡ −(K0 + 1)
(mod g). So, read row by row, an accepted word is the base-B expansion of
x0·κ^i mod g with the single fixed multiplier κ = −(K0 + 1), the same for
every N and h. The tableau rows would have to evolve by a fixed linear map
modulo g.

*The coset conclusion has a precise scope.* For alpha=A(J), independent of
the word variables, put P=K0+B^h. Then
(P+1)C ≡ 1-A(J) and (P+1)F ≡ P(1-A(J)) modulo M. If consistent these are
cosets of the subgroup above. Arbitrary deterministic or digit-wise ties need
not linearize: alpha=F² instead gives PF²+(P+1)F ≡ P. This observation
supplies no new completeness theorem.

*Consequence.* This is a substantive algebraic restriction, but the
nonlinearity of the machine does not by itself prove impossibility. Digit
blocks are decoded from the modular remainder using floors, carries and
masks; even an injective encoding need not turn that arithmetic into a
linear Boolean update. The subgroup argument alone does not establish that
two word variables are necessary. The narrower alpha=1 proposal does have
the decisive mask obstruction below. Other one-word or different-source
designs remain open and require complete compiler proofs.

### 2e. A decisive mask-budget obstruction and its scope

The [independent ordinary review](../../research/one-word-window-review/REVIEW.md)
proves the following finite-word lemma. Put q=2^u and let C,F,a,b be u-bit
words with C>=1. If

    C+F=q-1, (C-1) AND a=0, F AND b=0,

then popcount(a)+popcount(b)<=u+1. Indeed every bit of a AND b must be
set in C and absent from C-1. There is exactly one such bit, the least
significant set bit of C. The union/intersection population identity gives
the bound, without any parity or carry-free assumption.

The retained native masks a=MC*J+1 and b=MF_native*J-1 have combined
population u+2. Their exact repeated-mask identity therefore contradicts
alpha=1. Changing tile data or K0 cannot repair this while retaining those
mask conclusions and population budget. More generally the same argument
gives popcount(a)+popcount(b)<=u+popcount(alpha), so every power-of-two
slack is excluded. The unchanged low residues also give alpha=3 modulo4,
which separately excludes alpha=J.

There is a locally consistent selective-gap target: alpha=a AND b. Let
D=MC AND MF_native; the current coherent compact44/indexed tuple gives
alpha=D*J-1. This is a positive polynomial in the existing J, but it is
only a mask-level research lemma. No transport-compatible computation
encoding or complete nine-positive equation has been constructed from it.

The inherited rank controller is another concrete obligation. At fixed
N,h and alpha=A(J), two transport-compatible words differing by one safe
power-of-two dummy toggle would require (K0+B^h+1)*deltaC=0 modulo q-1.
Since deltaC is a unit modulo odd q-1, this is impossible at the canonical
padded dimensions. The old freely chosen pre-rank dummy family cannot be
reused unchanged. Coordinated changes or a new controller would need a
complete replacement proof. This excludes that inherited proof step,
not every possible controller or one-word encoding.

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

Each option needs a new soundness and completeness proof of the window
(the analogue of package44, Sections5–7, and `NativeSourceWindow`), whole
fixed coefficients and a rank controller. The current complete ten-positive
kernel offers92/283 and86/466 operation/degree tradeoffs. No nine-positive
size or degree bound is established by the proposed window changes.

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
