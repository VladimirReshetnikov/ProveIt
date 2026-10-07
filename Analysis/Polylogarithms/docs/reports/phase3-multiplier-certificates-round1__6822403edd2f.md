# Phase-3 round 1: multiplier certificates for the PolyLog stores

- Status: Report (results of the first proof-certification round)
- Created (UTC): 2026-06-10T15:52:44Z
- Repository HEAD: 07d0be954f6610ec4c94c25ff9be0e8ce360c827
- Normative companion: [`../proof-certificates.md`](../proof-certificates.md)
  (the certificate model, axiom policy, and checker contract)
- Code landed: [`../../tools/proof-core.wl`](../../tools/proof-core.wl),
  [`../../tools/proof-kit.wl`](../../tools/proof-kit.wl),
  [`../../tools/check-proofs.wl`](../../tools/check-proofs.wl),
  [`../../tools/generate-proof-certificates.wl`](../../tools/generate-proof-certificates.wl),
  [`../../tools/prove-ft-rules.wl`](../../tools/prove-ft-rules.wl)
- Store landed: [`../../identities/proof-certificates.wl`](../../identities/proof-certificates.wl)

## 1. What changed

Before this round, every identity in the PolyLog stores carried one badge:
*numerically verified to ≳ 25 digits*. After it, the concrete closed-form
values carry a second, qualitatively stronger badge: **derived** — a recorded,
machine-checkable certificate exhibiting the value as an exact linear
combination of verified functional-equation instances, replayed with no
search and no numerics in the certification path by an independent checker
that runs under the project's one-command regression guard.

Headline numbers:

| target store | concrete targets | derived | axioms (definitional) | unproved |
|---|---:|---:|---:|---:|
| `functional-equations.wl` values | 19 (+3 `Li_n(−1)` witnesses) | 19 | 3 | 0 |
| `dilog-special-values.wl` | 5 | 5 | — | 0 |
| `cyclotomic-values.wl` | 17 | 17 | — | 0 |
| `discovered-polylog-pslq.wl` | 37 | 4 | — | 33 |

Every *curated* value in the corpus is now derived — including all 17
cyclotomic values (the q=8 family included, see §3.4) — relative to the axiom
layer spelled out in the normative doc: the classical laws of
`functional-equations.wl`, four definitional pins, Euler's evaluation of
`ζ(even)`, trigonometric values at rational angles, and `RootReduce` as the
exact algebraic oracle.

The flagship aesthetic result of certificate compaction: `Li₂(½)` is a
**one-instance certificate** (Euler reflection at its own fixed point), and
each golden-ratio dilog carries exactly the classical four-equation linear
system (reflection + duplication + Landen + inversion at golden points, the
coincidence `1 − 1/φ = 1/φ² = (1/φ)²` doing all the work).

## 2. The model in one paragraph

A certificate stores law *names* + concrete substitution strings (never
expressions — a corrupted certificate cannot smuggle in a false instance) and
two exact multiplier vectors over a canonical real/imaginary splitting of the
instances. Validity means the claim `lhs − rhs` equals the recorded linear
combination **identically**: every inert `PolyLog`/`PolyGamma` atom
coefficient cancels `RootReduce`-exactly, and the elementary residual is
killed by a dedicated sound zero test (certified principal-branch log
normalization + certified multiplicative log-basis reduction + formal
coefficient comparison). Numerics appear in exactly two proposal/guard roles:
proposing root-of-unity decompositions that exact algebra then certifies, and
the per-instance branch-domain guard (an instance violating its law's branch
domain is generically numerically false and is rejected). Linear systems
subsume orbit words, fixed-point arguments, and multi-value systems in one
format.

## 3. Mathematical findings

### 3.1 Schwarz conjugation is a necessary axiom

The anharmonic orbit of `i` is the six-point family `{i, −i, 1±i, (1±i)/2}`,
and inversion and duplication at `i` produce the *same* sum relation. The
full system of reflection/inversion/Landen/duplication instances over the
orbit is therefore **rank-deficient by exactly one dimension**, and the
missing direction is precisely `Li₂(z̄) = conj Li₂(z)`. No combination of the
single-variable transformation laws separates `Li₂(i)` from `Li₂(−i)`; the
conjugation symmetry had to be added to the law store as an axiom (with its
classical justification: real Taylor coefficients + reflection principle).
This is obvious in hindsight — the transformation laws are Möbius/algebraic
in the argument and blind to complex conjugation — but the linear algebra
*measured* it: exactly one missing dimension, no more.

### 3.2 Catalan is definitional; the rest of the family is not

`β(2)` admits no derivation from the stored laws: it enters every certificate
that needs it through one of two recorded definitional pins (`Im Li₂(i) =
Catalan` or `ψ₁(1/4) − ψ₁(3/4) = 16·Catalan`, both termwise series
identities). By contrast `Li₂(−1) = −π²/12` (duplication at z=1), the four
golden values, `Li₃(½)`, the golden trilog `Li₃(1/φ²)`, and `Li₂(2)` are all
honestly *derived*. The certificates make the classical folklore precise:
within this law vocabulary, the dilog world at weight 2 has exactly one
"new constant" on the imaginary line, and it is Catalan.

### 3.3 Prime q needs the full-sum multiplication row

For the cyclotomic values `Li_n(e^{2πip/q})` the polygamma vocabulary
(reflection + multiplication + `ψ_m(1) = ±m!ζ(m+1)`) pins the `ψ`-grid. For
*composite* q the proper-divisor multiplication instances suffice; for
**prime** q the only `ψ`-sum relation is the full multiplication row `d = q`
(`ψ_m(1) = q^{−m−1} Σ_k ψ_m(k/q)`), and it is exactly the source of the
irrational coefficients — e.g. the `√5·ζ(3)` terms in the q=5 trilog closed
forms. Omitting `d = q` cost precisely the prime-q certificates and nothing
else.

### 3.4 The trusted trig layer must be applied, not assumed

Wolfram auto-evaluates `Sin[π/4]` but **not** `Sin[π/8]`: the q=8
certificates initially failed because `Csc[π/8]²` survived as an opaque atom
in the formal zero test while being numerically zero all along. The fix is a
one-line policy: trig at rational multiples of π is part of the declared
trusted base, applied explicitly (`FunctionExpand` + `RootReduce`) during law
instantiation and residual checking. Lesson for certificate systems
generally: a "trusted constant layer" is only trusted if the checker actually
*invokes* it — silent reliance on auto-evaluation makes the trust boundary
version-dependent.

## 4. Engineering notes (banked for future rounds)

- **`Return[expr, Module]` exits the innermost `Module`.** Wrapping the
  certificate-compaction call in `Module[{cc = …}, Return[…, Module]]`
  silently discarded every found certificate; the regenerated store read
  "0 derived" before the bug was found. `With[{…}, Return[…, Module]]`
  restores the intended non-local return. (The wrong store was caught before
  commit by the entry-count check — counts in headers earn their keep.)
- **Pools are a budget.** The Kummer-class bridge instances (Square
  inversion, Abel four-term, Duplication–Landen) are essential for
  *between-orbit* targets (the FT reduction rules) but fatten ℚ(i)-family
  pools past the per-target time budget; they are now an opt-in pool option.
- **One row contract.** Generator and checker share the literal
  `CertificateRows` function, so the multiplier indexing cannot drift between
  the two — worth copying into any future certificate-shaped tooling.

## 5. The open frontier

1. **FT-437 sweep** ([`prove-ft-rules.wl`](../../tools/prove-ft-rules.wl), in
   flight as this report is written): the order-2 pass with Kummer pools is
   deriving real-argument rules (`Li₂(−8/9)`, `Li₂(−6/7)`, `Li₂(−4/5)`,
   `Li₂(−3/4)`, …) at 5–15 instances each; complex-argument rules currently
   fail and will need ℚ(i)-aware pool extensions (their closed forms mix
   `Catalan`, `ArcTan` values, and cross-orbit dilogs).
2. **The 33 unproved discovered-PSLQ values**: genuinely exotic (the
   `Im Li₃` family at `ℚ(i)`/`ℚ(√3)` points). Expected to need the
   two-variable five-term law *instanced over algebraic pairs* — instance
   generation over a 2-parameter family is the next qualitative step for the
   generator. Four already certify, including the cross-project bridge
   `Im Li₃((1+i)/2) ↔ Im Li₃(1+i)`.
3. **P2 (single-valued certificates)**: the Bloch–Wigner five-term machinery
   is in the law store but unused by the generator; `D(z)`-based certificates
   would remove the branch-domain numeric guard for the real-analytic subset
   of claims — the natural next rigor upgrade.
4. **P4 (formalisation)**: the certificate replay (linear algebra + the
   elementary zero test) is a small trusted core; Rocq is available locally,
   and the law statements are first-order — a plausible formalisation target.

## Addendum: final round-1 coverage (sweeps concluded)

- Added (UTC): 2026-06-11T00:14:19Z
- Repository HEAD: fa11dfa9f97d34e5b358dd387fe9a458510be72b

All round-1 sweeps have concluded. The certificate ledger now replayed by
[`check-proofs.wl`](../../tools/check-proofs.wl) under `tests/run-all.ps1`
(**ALL GREEN**, 191 derived + 4 definitional, zero failures):

| store | derived / attempted | notes |
|---|---|---|
| `proof-certificates.wl` | 45 + 4 definitional | every concrete curated value |
| `proof-certificates-ft.wl` | 61 / 83 | real-argument order-2 FT rules; 22 holdouts need five-term instances beyond the current candidate family |
| `proof-certificates-gamma.wl` | 85 / 100 | FT-Gamma rules with argument denominator <= 40, via the Koblitz-Ogus-complete `GammaGridLawPool` lattice in fresh-kernel chunks; merged by `merge-gamma-certs.wl` |

Frontier (documented, not attempted further this round): the 15 q=40-grade
no-certs (sine-product `RootReduce` blowups, `Gamma(11/40)`..`Gamma(19/40)`
zone), the q>40 Gamma tail (cyclotomic-unit arithmetic or DFT certificate
transport), the 22 FT holdouts, and 33/37 exotic discovered-PSLQ values.

Side discovery during the same stretch: the CM-lattice polygamma program
(Eisenstein row-sums at imaginary-quadratic points through class number 3) --
see `polygamma-complex-arguments-cm-lattices__d41f7be20c61.md`.

## Addendum 2: the FT holdout sweep (round 2) — 61/83 → 82/83

- Added (UTC): 2026-06-11T06:09:00Z
- Repository HEAD at sweep start: 1fe53f9e8 (see final commit for landed HEAD)

The 22 round-1 holdouts fell to three cumulative generator upgrades, all in
[`../../tools/proof-kit.wl`](../../tools/proof-kit.wl) /
[`../../tools/prove-ft-rules.wl`](../../tools/prove-ft-rules.wl), leaving
**one honest no-cert** (82/83 real-argument order-2 FT rules derived).

1. **`FiveTermPairPool` — atom-closure five-term pairs.** Pairs `(z, w)`
   drawn from the closure (the claim's dilog arguments plus every dilog
   argument of the companion pool instances), admitted only when all five
   points of the two-variable five-term relation land back in the closure.
   This alone was *not* enough: the first holdout diagnostic (`Li₂(−2/7)`)
   failed in ~1 s — rank-deficient, not slow. The missing dimension was the
   **structured one-parameter pair families**: pairs `(x, 1−x)`,
   `(x, x/(x−1))`, `(x, −x)` over a global small-height rational grid, whose
   partner atoms cancel via ONE companion law instance added alongside
   (reflection / Landen / duplication at `x`), so only the three *derived*
   points need closure membership. `Li₂(−2/7)` fell to the five-term at
   `(−2, 3)` — a 6-instance compacted certificate. 16 holdouts fell here.
2. **Square-root argument seeding** (driver). A claim-side quarter
   multiplier on a perfect-square atom (`¼·Li₂(9/64)`, `9/64 = (3/8)²`) is a
   duplication ladder; the rule's argument set is widened by the square
   roots of perfect-square rational arguments before pooling, so the rungs
   `Li₂(±3/8)` get orbits. `Li₂(−2/9)` fell here.
3. **Height-weighted cluster retry** (driver). The hardest rules come in
   vocabulary clusters chaining through one another's arguments — the
   five-term at `(−1/10, −5/6)` has quintuple `{1/12, −1/10, −5/6, −1/5, −1}`,
   linking `Li₂(−1/10)` (rule 59) to `Li₂(1/12)` (rule 109). On failure the
   driver pools the orbit vocabulary of every slice rule sharing ≥ 2 dilog
   arguments with the claim and rescans pairs over the union closure.
   Ranking the related rules by **height-weighted** overlap mattered: shared
   compound atoms (`1/14`, `36/49`) name the orbits whose big-prime points
   (13s, 17s) must cancel, while shared basis atoms (`1/3`, `1/5`) carry no
   information — the unweighted top-4 cut dropped the 13-carrier rule 60 and
   cost `Li₂(−5/8)`, `Li₂(−3/10)` a whole retry round. No related *claim* is
   ever used — only law instances over its argument orbits, so no
   circularity enters any certificate. 5 holdouts fell here (1019 s worst
   case, 80-instance certificate for `Li₂(−4/7)` in `deep` mode: 8 related
   rules, closure cap 500, pair cap 600, grid height 24).

**The honest no-cert: FT 21, `Li₂(−7/10)`** — the deepest ladder in the
slice (10 residual dilogs, `{1/35, 1/18, 1/7, 25/144, 1/5, 2/7, 1/3, 2/5,
3/7, 64/81}`). Rank-deficient even at the deep caps above with raised pool
budgets (3000 s cluster-pool build, 1800 s search): the orbit pairs
`1/18 ↔ 1/35` demand an *internal* 17-flavored cancellation
(`−17 ∈ orbit(1/18)`, `−34 ∈ orbit(1/35)`) that no implemented pair family
reaches — the candidate bridge quintuples (`(−17, 2)` → `{−34, −17, 2,
17/35, 36/35}`) carry points like `2` and `36/35` outside every pooled
orbit. The natural next lever is second-order stray matching (admit pairs
with one off-closure derived point when strays pair up across instances) or
ladder relations beyond the stored law set.

Workflow notes: the sweep ran as fresh-kernel chunks of 2–6 rules
(`prove-ft-rules.wl 2 real ids=...`), each run MERGING into
`proof-certificates-ft.wl` (id-filtered runs preserve existing entries and
replace re-derived targets); every certificate replayed through
`check-proofs.wl` at generation time and again under `tests/run-all.ps1`.
Kernel peak ~3.6 GB on the heaviest cluster chunk — chunking remains
mandatory on this machine.

Ledger after round 2: **212 derived + 4 definitional certificates replay
green** (45 curated + 82 FT-polylog + 85 FT-Gamma).
