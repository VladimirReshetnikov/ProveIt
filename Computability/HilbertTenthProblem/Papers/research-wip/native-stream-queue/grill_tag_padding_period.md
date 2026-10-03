# Whole-period zero padding and the ordinary Grill input boundary

For any fixed Grill program of period m, appending q·m zero bits to the **end** of its initial little-endian queue preserves halting. If the original first halt is at T, the padded run first halts at exactly T+q·m. This includes all-zero and empty initial words. For ordinary positive input x, the native compiler's existential choice of arbitrarily large input width therefore reduces semantically to **m canonical widths**, one per residue modulo m.

A useful compiler consequence is that the existing width definition `P0=3x+Z0` can be weakened to `P0=x+Z0` in a separately reviewed native compiler. The latter saves one multiplication while recognizing the same existential x-language. This is a language equivalence after existentially quantifying all witnesses, not a same-tuple zero equivalence or polynomial identity. The frozen native219 source is unchanged by this packet.

## 1. Exact coupling, including premature-halt concerns

Let the fixed program be `(n_0,...,n_(m−1))`, with m>=1. One macro removes a front bit. A one appends `0(10)^n_p`, and a zero appends nothing, before the phase advances modulo m. The empty queue halts; no transition fires from it. Allow any fixed initial phase sigma for the lemma.

Let w be an initial word of length L and k>=0. During the first L steps, the original run cannot halt before all initial symbols are consumed: at each earlier time the remaining initial suffix is still in the queue. Output is always appended after that suffix. This does not assume that a bit can consume output created in the same step.

Let G_sigma(w) be the concatenation of appendants selected by the L initial symbols, at phases sigma through sigma+L−1. At time L, the run from w has state

```
(phase sigma+L mod m, queue G_sigma(w)).
```

The run from w followed by k zeros processes exactly the same first L bits at exactly the same phases and produces exactly the same appendants. Its state at time L is

```
(phase sigma+L mod m, queue 0^k G_sigma(w)).
```

It next consumes those k zeros without output. Until the last such zero is consumed, the padded queue is nonempty. Thus its state at time L+k is

```
(phase sigma+L+k mod m, queue G_sigma(w)).             (1)
```

If k=q·m, this is exactly the original state at time L, including program phase. Determinism now identifies every subsequent step of the two runs with a time offset k. If G_sigma(w) is empty, the original first halt is exactly L and the padded first halt is exactly L+k. If it is nonempty, neither has halted at its respective matching time; their future first halt, or infinite continuation, is identical up to that offset.

For w empty, L=0 and G_sigma(w) is empty; the same argument says that k zeros halt after k steps. This closes the boundary case without applying a nonexistent transition to an empty queue.

We have proved, for every q>=0,

```
Halts_sigma(w) iff Halts_sigma(w 0^(qm)),
T_sigma(w 0^(qm))=T_sigma(w)+qm                       (2)
```

whenever the first-halting time is finite. Nonhalting is preserved as well. An infinite-run conclusion does not rely on a bounded simulation cutoff.

## 2. The exact finite union of padding residues

For positive x, let w_ell(x) be its ell-bit little-endian binary word, including zeros at the end. The strict strong cone `P0=2^ell>3x` is equivalent to

```
ell >= ell0=(3x).bit_length().
```

Every permitted ell has a unique expression

```
ell=ell0+r+qm,       0<=r<m, q>=0.
```

The words differ only by q·m terminal zeros. Consequently

```
exists ell with 2^ell>3x and Halts(w_ell(x))
 iff OR_(0<=r<m) Halts(w_(ell0+r)(x)).                 (3)
```

For each individual residue, the first-halting time at ell0+r+qm equals the canonical first-halting time plus q·m. The canonical width need not be the same residue for every x; ell0 depends on the input's bit length.

This is a semantic finite-union theorem for a fixed program. It does not assert that computing bit length, its phase residue or an encoded canonical word is free inside an arithmetic circuit. The native compiler already pays its existential width and full word relation; equation(3) clarifies which choices that relation permits.

## 3. One extra zero can change the answer

The period condition is substantive even within the native input cone. Take program `(2,0)` and ordinary input x=1.

* At width4, the initial word is `10`. It first halts after9 steps.
* At width8, the initial word is `100`. At step7 it reaches phase1 and queue `00101001010`, and reaches that identical full configuration again at step19. This exact period12 cycle proves nonhalting.

Both widths satisfy P0>3x. Thus a one-zero extension changes halting truth. Period2 is the smallest possible declared period for such an example: for period1 every number of added zeros is covered by(2). Input1 is the smallest positive integer. No general minimum for exponents, cycle length or source description size is claimed.

Even when both runs halt, a nonperiod extension need not simply add its length to the running time. Program `(1,0)`, x=1, halts after6 steps from `10`, but after10 from `100`, not after7.

The program used in the preceding native examples also depends on the padding residue. For `(0,1,1)` and x=2, the three canonical strong-cone words are:

| Width / initial word | Certified behavior |
|---|---|
|8 / `010`|Returns to phase0 and `010` after3 steps; nonhalting.|
|16 / `0100`|Reaches phase0 and `0010` at step3, repeating that full configuration at step6; nonhalting.|
|32 / `01000`|First halts after9 steps.|

The checker records the full state sequence for each case, including the actual cycle entry phase. It never declares a run nonhalting merely because a finite step limit was reached. The full traces also include `(1,0,0)`, x=1, where width4 is a period3 cycle while widths8 and16 halt at7 and8 respectively.

## 4. Equal input languages from the weak and strong cones

Now allow the weaker cone `P0=2^ell>x`, whose least permitted length is `ellweak=x.bit_length()`. If a permitted weak-cone word halts, append2m zeros. By(2) the extended word still halts; its new width is

```
P0'=2^(2m) P0=4^m P0>3x,
```

since m>=1 and P0>x. It lies in the original strong cone. Conversely every strong-cone word is already in the weak cone. Thus the two existential padded-input halting languages are exactly equal for every fixed Grill program.

There is also an exact canonical-residue correspondence. Pair each of the m weak canonical lengths with the strong canonical length having the same residue modulo m. The strong representative equals the weak representative plus q·m for q in{0,1,2}, since the least strong length exceeds the least weak length by only1 or2. Their halting truth agrees, and finite first-halting times differ by exactly q·m.

## 5. Paid native compiler corollary and its limits

The complete [native word-closure compiler](grill_tag_native_word_closure.md) uses positive x,Z0,Vfinal and computes

```
P0=3x+Z0,
Ufinal=P0*Vfinal+x.
```

Its sentinel proof needs only P0 dyadic and `0<x<P0`. Therefore the separate source replacement

```
P0=x+Z0
```

removes exactly the fixed multiplication by3. The unchanged positive Z0 proves x<P0; the already paid `P0 AND(P0−1)=0` lane proves dyadic width. The boundary still decodes the exact word equation `h=w G(h)`.

Every pretyping height argument remains valid. On all supplied positive tuples, P0>=2, Vfinal>=1 and x>=1, hence

```
Ufinal=P0*Vfinal+x > P0, Vfinal, 1,
D=Ufinal+phase_initial+rho >=5.
```

Thus D exceeds every endpoint needed for the history-range proof, and it exceeds phase_initial before decoding the phase-flow equation. In particular the retained native construction's D>=4 requirement holds. The global positive slack proof and the extra dyadic-width lane use these individual bounds, not the stronger inequality P0>3x.

The modified source would recognize the weak-cone language, which the theorem above identifies with the old strong-cone language. This justifies **one fewer multiplication** in a separately guarded full-source child (native219 would become218). This packet does not edit that parent or emit the child, and it does not count this as an all-value source identity.

A new weak-cone zero can decode to a run at a width excluded by the old source. To prove the reverse existential implication, recover the actual first halting run, extend its initial word by a whole-period padding, and rebuild the packed histories, height, bound slacks and native Pell extension for that new run. Existing witness coordinates need not survive that reconstruction. The claim is

```
for each positive x,
  exists positive old witnesses: F_old=0
    iff exists positive new witnesses: F_new=0,
```

not equality of the two full positive zero sets or a bijection of their fibers.

This sharpens the still-open ordinary-input universality obligation: a fixed Grill recognizer needs a correct union of its m canonical padding-residue behaviors. It need not be separately invariant under every one-zero extension, which is false in general. Proving that this union is a specified universal input language still requires an actual finite program and paid program/input decoding. The informal block-encoded Genera construction does not supply that proof merely from abstract universality.

## 6. Executable evidence and reproduction

The [standalone checker](grill_tag_padding_period.py) authenticates the frozen direct Grill source before comparing its literal macro rule with an independent simulator. It checks the exact prefix coupling for programs of periods1–4 with exponents0,1,2, all words of length0–5, all initial phases and zero through three whole-period padding blocks. These tests include empty and all-zero words.

A separate bounded classifier supplies exact halts or repeated full-state cycles. Runs that reach a word-size or time cutoff are explicitly unresolved and do not support a nonhalting claim. For every certified case it checks the appropriate first-halt shift or an exact shifted cycle. The receipt records107,352 exact prefix couplings,26,838 comparisons to the pinned macro,1,364 exact first-halt shifts and1,038 shifted cycle checks. Its1,632 bounded canonical runs include431 explicitly unresolved cases. It also verifies23,040 canonical width factorizations and4,608 weak/strong residue pairs for x<=128 and m<=8, plus20 malformed-call rejections. All counterexamples above have complete finite halt or cycle certificates in the [receipt](grill_tag_padding_period.json).

Run `python grill_tag_padding_period.py --expect grill_tag_padding_period.json`; `--source PATH` selects the exact pinned direct simulator. The checker has no repository imports, ignores Python bytecode by compiling the authenticated source bytes itself, restores no global module cache because it adds none, and writes only with `--output`. Saved-receipt comparison is recursively type-sensitive after JSON normalization. The general theorem is the exact coupling proof, not an extrapolation from these finite tests.
