# Independent review of the final complete86/87 first-root wrapper

**PASS; no source, theorem, ledger, or metadata correction requested.** The normalized asymmetric universal polynomial is **86=48M+38A**, exact degree **179**, and the ordinary-strong form is **87=47M+40A**, exact degree **135**. Both retain the ordinary positive input, all19 strictly positive witness slots and the selected parent’s full fixed-program universality contract. The new slot is explicitly named `tau_root`, replacing `tau_gap`.

This review is self-contained and targets the final `complete86_factored_first_root` trio, not the preliminary candidate JSON. Authenticated pins are:

- Compiler: `29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f`.
- Receipt: `2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e`.
- Mathematical note: `9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b`.

All five selected-parent source/receipt pins are independently checked. The parent sources are retrieved from the authenticated `complete75_asymmetric_scale_tradeoffs.json`, rather than trusted because the new wrapper returned them. The entire final source and proof note were read. The new wrapper executes no historical compiler module; this reviewer executes its authenticated bytes directly, bypassing `.pyc` resolution. No repository file is changed.

## Full coordinate identity and positivity

Use the original definitions `X=wq`, `Y=sq³`, `E=XY`, `k=eta+zeta`, and

```
V=XY², L=Vk=E*(kY).
```

Here `L` is the actual `first_root_base` register. The original supplied first-gap coordinate is `g=tau_gap`, and its first factor is

```
N0_old(g)=g²+L*(2g−k).
```

Replace that supplied slot with the named positive ordinary first root `T=tau_root` and use

```
N0_new(T)=T²−L*(L+k).
```

Since `L` is independent of this slot, the maps `T=L+g` and `g=T−L` are inverse polynomial coordinate automorphisms over the integers (and over any commutative ring). Direct expansion gives `N0_new(T)=N0_old(T−L)`. The source confirms that `tau_gap` had only two direct old consumers: its square and doubling. The other seven factors have no dependence on it. Thus the **complete** polynomials satisfy

```
F_new(T,other)=F_old(T−L,other)
F_old(g,other)=F_new(L+g,other).
```

These are not same-coordinate polynomial equalities. The unchanged-coordinate values generally differ.

The restriction to the full positive integer zero sets needs a separate argument, and it is short. At any complete new integer zero the eight integer factors multiply to one, so `N0_new=epsilon` with `epsilon∈{−1,1}`. The inherited positive-coordinate/compiler contract gives `V>1`, `k>=2`, and `L=Vk>0`. Therefore

```
T²−L² = L*k+epsilon >= V*k²−1 > 0.
```

Since the supplied `T` is positive, `T>L`; consequently the restored `g=T−L` is a positive integer. Every other supplied coordinate is unchanged. The exact full polynomial identity now gives a full old positive zero, to which the parent's established sign recovery and universal compiler theorem apply. **No negative-Pell exclusion, decoded mask, strong-rank lemma, or first-factor +1 conclusion is needed before this restoration.** Conversely, an old positive zero gives positive `T=L+g` and the same new zero. The maps are inverse on all supplied positive integer zeros, not merely on a canonical Pell subfamily. They do not map the whole positive orthant bijectively: a general positive off-zero `T` may have `T<L`.

All original ordinary-input, fixed compiler mask/layout, scale, ratio, strong norm, auxiliary norm and synchronization obligations are retained through that full-zero bijection. No runtime horizon is introduced and no astronomical witness is materialized by the test fixtures.

## Paid source and exact degree

The changed first-norm subcircuit counts `L` in both schedules:

- Old: `L`, `g²`, `2g`, `2g−k`, `L*(2g−k)`, and their final sum: six gates, three multiplications and three additions/subtractions.
- New: `L`, `T²`, `L+k`, `L*(L+k)`, and the final difference: five gates, three multiplications and two additions/subtractions.

`kY` remains paid because the ratio numerator still uses it. The verifier independently emits the literal rewrite, including the `tau_gap` to `tau_root` coordinate rename, and compares it to both complete outputs of the frozen wrapper and both receipt sources. Every old surviving gate remains paid; all eight factors, seven final product multiplications and the last subtraction of one remain in the complete output. All emitted gates are ancestors of that output. The free-coordinate set is exactly the parent's after that one coordinate rename, including ordinary input and all six fixed numeral ports.

Let `Q0=(B−1)J`, `k0=eta+zeta`, `gamma0=rho+sigma`, and `Ctop=Q0−F−Z−alpha−2d*x`. The old first-root base has exact degree 11 and leading form

```
L0 = k0*w*s²*Q0^7.
```

The new first factor has leading form `−L0²` and exact degree 22; its free `T²` term has degree two, and `L*k` has degree twelve. The parent's other exact factor degrees and leading forms are unchanged. Therefore the new ordered degree lists are

```
normalized: 22,18,32,56,7,3,34,7   (sum179)
ordinary:   22,18,32,24,7,3,22,7   (sum135).
```

The respective complete leading forms are

```
−32*Q0^108*h²*gamma0*delta²*i^4*k0^13*w^18*s^30*Ctop,
+32*Q0^80*h²*gamma0*delta²*i²*f²*k0^9*w^14*s^22*Ctop.
```

Both are nonzero polynomials for every admissible fixed `B`. Thus the degree assertions are uniform across the inherited fixed compiler slices, rather than just degrees witnessed by one numeric program. The exact numerical expansions below independently check the literal-source leading coefficients; the uniformity and upper bounds follow from these displayed forms and the authenticated parent proofs.

## Independent final-source and API checks

The executable independently emits both literal rewrites from the pinned parents, compares every complete source row against the wrapper and saved receipt, and verifies every paid gate is live. Its independently reconstructed metadata includes both full ledgers, the exact factor-degree lists,85/86 certificate operations with one comparison,19 current positive witnesses, the six unchanged fixed-numeral ports, and ordinary input `x`. Both fair parent baselines are checked. The renamed `tau_root` has exactly one direct current consumer, its square; no `tau_gap` remains in either emitted source.

An exact sparse expansion in independent atoms `T,L,k` proves the first-factor identity. A separate expression-DAG interner then compares all eight factors and the complete finalizer using only that proved cut:18 full factor/finalizer identities. This is a whole-polynomial proof; it does not rely on sampled equality. Supplementary independent checks cover512 complete coordinate identities in both directions, including256 signed cases and64 rational cases, plus55,552 unchanged-register comparisons. The author’s low-level evaluator is also compared with the independent executor. Four exact integer univariate evaluations expand **every coefficient of the emitted full polynomial** and attain179/135 with the stated leading coefficient. The uniform degree proof is the displayed leading-form argument, not a finite sampling claim.

The final `rewrite(root, normalized, supplied)` API accepts only an exact Boolean mode and, when supplied, the complete canonical source of that selected parent. The review confirms573 malformed-parent/mode rejections. These include every gate’s operation/name/container mutation, floating-point and Boolean substitutes for integer coefficients, truncated/extended/wrong-mode/new-child sources, and deliberately algebraic no-ops: commuting a multiplication or appending `+0` to the final output. Rejecting a no-op source is appropriate here because the documented contract is canonical source equality, not arbitrary polynomial equivalence.

Six independent mutation checks confirm that returned parent records and old/new source lists do not affect future calls. Two repeated-call checks first build successfully from a private parent copy, then alter either the authenticated source or JSON; both are rejected despite the previous successful call. The recorded positive off-zero inverse boundary is evaluated independently and has both a negative restored gap and nonzero complete output. This checks the note’s distinction between a full positive-zero bijection and a nonexistent positive-orthant bijection.

`evaluate`, `inspect`, and the polynomial-expansion helpers are low-level arithmetic/audit routines, not a claimed independently guarded natural-domain compiler interface. The strict selected-parent contract resides in `rewrite`. This distinction is reflected in the review rather than demanding an unrelated public-packet API.

After inspection, the reviewer reruns the entire author verifier and requires recursive type-sensitive equality with its pinned saved receipt. Both the review writer and a fresh read-only saved-receipt replay from `/` pass. No full compiled-program Pell zero is materialized; finite component and signed/rational fixtures supplement the exact source and positivity proofs. No Lean verification, new single-scalar program decoder or globally optimal circuit claim is made.

## Reproduction

Use Python3 with SymPy, required by the frozen author verifier invoked at the end. The inherited parent compilers are not imported. In this workspace the research environment is `/tmp/diophantine-research-venv/bin/python`; adjust the interpreter and paths elsewhere.

```sh
/tmp/diophantine-research-venv/bin/python review_complete86_first_root_source.py \
  --root /path/to/native-stream-queue \
  --expect /path/to/review_complete86_first_root_source.json
```

The default compiler location is `ROOT/complete86_factored_first_root.py`. During isolated review use `--compiler /path/to/complete86_factored_first_root.py`; its authenticated `.json` and `.md` companions must be adjacent. `--output PATH` writes an independent receipt. The reviewer rejects `python -O` and compares saved receipts recursively with exact types. All dependencies and receipts are pinned; neither execution nor output depends on a hard-coded scratch path.
