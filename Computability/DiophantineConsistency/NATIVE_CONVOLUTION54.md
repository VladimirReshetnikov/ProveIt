# Compact54 cyclic convolution and the carry bound

Four new Lean modules close the arithmetic carry step between the native
window and pointwise digit-mask tests. They do not supply the remaining
assignment-support, phase-synchronization or machine-calibration theorems.

`NativeCyclicConvolution` represents an `n`-digit word by a function
`ZMod n → Nat`, for any nonzero `n`. It proves

```
word(rho, convolution(a,c)) = word(rho,a)*word(rho,c)  (mod rho^n−1).
convolution(a,c)[k] <= mass(a)*D                      if c[i]<=D.
```

The finite-stencil interface folds every original exponent modulo `n`.
Its folded mass equals the sum of its original coefficients, even when
several exponents collide. Its convolution equals the original stencil
sum acting on the cyclic digit array. Consequently a budget
`mass(a)*D+T+2 <= rho`, together with `r[i]<=T`, gives digits strictly below
`rho−1` and a word strictly below `rho^n−1`. This also excludes the exceptional
all-`rho−1` representation of the zero residue. Transport congruence then
determines the word exactly, and a packed binary mask test is equivalent
to all its digit-mask tests. No accepted-clause or one-hot hypothesis is used.

`NativeStencil54` defines the literal coefficient recipes from the whole
compact54 tuple, at source pin
`4b4349064a750ba6347293b55874a7f92abdd0db`. It uses the checked 457-mode table
and receiver/copy bit coefficients from the six local-decoder modules.
There are 520 assignment positions, including the two zero-coefficient
dummy positions. The full current/spatial coefficient recipe is

```
rho^33 + rho^68 + rho^664 + rho^1268
 + sum_(e,ce) ce*(rho^(2409−e)+rho^(3015−e)) + rho^(4831+46).
```

Thus it retains both clause bands, all four current-copy offsets, and
the spatial term from `K=DC+rho^4831*DR`, `DR=rho^46`. Lean checks

```
sum ce = 21018633715859000553417,
raw stencil terms = 1045,
raw stencil coefficient mass = 42037267431718001106839,
3*mass + 3*2^87 + 2 <= 2^89.
```

The definition `rawWord` is a symbolic exact coefficient, avoiding expansion
of the 434054-bit integer. Its equality with a materialized coefficient port
is an explicit binding premise, not an inferred consequence of port bounds.

`NativeCyclicRotation` defines the actual digit-level normalization of a
binary shift, including the carry from the preceding digit and the cyclic
last-to-first carry. For `W=89*t+epsilon` it proves that the resulting word
is congruent to `2^W*word(c)`. For every input digit at most three, every
normalized digit is at most `3*2^87`, uniformly over all partial phases.
It also proves that phases 1 through 87 have even digits; at phase 88 the
odd digit is precisely the preceding digit's upper bit. No phase alignment
is assumed by these theorems.

`NativeWindowConvolution54.source_convolution_mask_digits` combines these
results with the proved source-to-window theorem. It derives the strict
bound `F<q−1` from the source's positive gap and slack. It derives the
transport congruence from the exact old-z transport and normalizes its
binary temporal shift. For `rho=2^89`, the remaining premises are exactly

```
c : ZMod n -> Nat,          c[i] <= 3,
m : ZMod n -> Nat,          m[i] < rho,
word(rho,c) = C,
q = rho^n,
K = rawWord(rho),
word(rho,m) = MF_native*J−1.
```

Under the existing arithmetic `NativeSourceMask.Interface`, its conclusion
is the actual pointwise test

```
(convolution(foldedStencil,c)[k] + normalizedTemporalShift(c)[k]) AND m[k] = 0
```

for every cyclic position. The coefficient budget, temporal digit bounds,
strict residue bound and transport are proved inside the theorem.

The next concrete bindings are still open: derive the sparse Boolean/two-bit
assignment digits and forced Start bit from `(C−1) AND (MC*J+1)=0`; bind the
whole symbolic `K`, low mask and high mask to the fixed tuple; and prove
the current/spatial basis identities and clean-band selection for these
digits. The local decoder then enables the anchor argument to eliminate
the partial phases and align the whole-cell shift. A matching marked Wang
tiling must still be extracted and related to the actual Lean K215 machine.
The reverse construction and the internal ZFC consistency biconditional
also remain open. None is replaced here by a supplied correctness premise.

All 43 public theorems have dedicated axiom checks in the four corresponding
`Lean/checks` files. The only axioms are `propext`, `Classical.choice` and
`Quot.sound`; several finite arithmetic facts use only `propext`.

The subsequent [origin checkpoint](NATIVE_ORIGIN54.md) proves the exact
symbolic lowMC residue and derives the Start digit C modρ=1 from the actual
source masks. The remaining non-origin support and phase/basis work is
not inferred from that fact.
