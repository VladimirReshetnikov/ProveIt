# Fixed-coefficient physical-position proofs

## Retained result and conservative withdrawal

Two **proof-only** changes in `CurrentControllerPositions2011.lean` remove
**4 physical and 4 nonblank lines**, with no new helper, import, declaration,
definition, hypothesis, or module dependency. The complete file changes from
178 to 174 physical lines and 148 to 144 nonblank lines. Every Lean candidate
is **UNCOMPILED**: source/static/finite checks establish neither elaboration,
kernel acceptance, axiom footprint, nor compilation-speed improvement.

**The earlier optional-branch trial is withdrawn.** Late packet zq proposes
retiring the optional-support branch. Since every earlier proposal is assumed
applied, `optional_next_lt`, `optional_stride_lt`, and `position_ne_three` earn
no new credit, even if wrappers could be preserved in one adoption choice.
Their candidate edits and isolated patches have been removed. The delivered
candidate changes only `position_budget` and `position_injective`.

The fixed, small controller auxiliary is `120199`
(`CurrentControllerData2011.lean:24`). Unfolding it makes these two affine
position obligations linear. `pow_succ` exposes one final factor in the
budget proof, while `120199^k` remains a symbolic natural-number atom. No
literal kernel K, radix power, or enormous concrete exponent is evaluated.

| Retained proof | Original anchor | Candidate anchor | Body lines | Saving |
|---|---:|---:|---:|---:|
| `position_budget` | 24–31 | 24–28 | 6 → 3 | 3 |
| `position_injective` | 79–84 | 76–80 | 5 → 4 | 1 |
| **Full helper-inclusive module** | complete file | complete file | **178 → 174** | **4** |

Source pin: `9d9d1123b39927d30363f1dcd53c23f0575c30ee`.
`manifest.json` binds complete source/candidate SHA-256 and Git blob hashes,
exact old/new bodies, counts, unchanged dependencies/checks, and the withdrawal.
Use `candidate/CurrentControllerPositions2011.lean` or
`patches/positions_combined.patch` for the retained pair.

Use **only the combined patch** to apply both changes. Never apply the combined
patch plus isolated patches. The two isolated patches are alternatives for
separate/selective single-edit trials against the original baseline; their
savings must not be added again to the combined four-line total. Do not
promise arbitrary sequential application of context-bearing isolated patches.
The two-order audit concerns exact proof-body replacements, **not** arbitrary
sequential unified-patch application. The integrated audit uses the combined
patch only.

## Mathematical argument

Write `a = 120199`, `q = a^k`, and `v = j.val`.

1. **Budget.** The canonical representative fact is `v+1 ≤ q`. Expanding
   `position` and the final successor exponent turns the goal into
   `2+120198*v+q+120199 ≤ 120199*q+3`. This is exactly
   `120198*(v+1) ≤ 120198*q`, so linear arithmetic proves it. The replacement
   retains the canonical bound and replaces coefficient positivity,
   multiplication transport, and `nlinarith` with local normalization/`omega`:

   ```lean
   have hv : j.val+1 ≤ auxiliary^k := ZMod.val_lt j
   simp only [position, pow_succ, auxiliary] at hv ⊢
   omega
   ```

2. **Injectivity.** The equality becomes
   `2+120198*i.val = 2+120198*j.val`. Linear cancellation gives equality of
   canonical values; the existing `ZMod.val_injective` gives equal cells:

   ```lean
   intro i j hij
   apply ZMod.val_injective
   unfold position auxiliary at hij
   omega
   ```

These are routine exact-client simplifications, not new mathematics, a new
API, or a new algorithm. The proof uses the maintained concrete auxiliary,
not a generalized assumption that every abstract auxiliary works.

## Preservation and exclusion boundary

All declarations, signatures, definitions, imports, options, comments, and
unmodified proofs are byte-preserved. `position` retains the canonical value
of `ZMod (auxiliary^k)`; `cell` retains codomain `ZMod (auxiliary^(k+1))`.
No ordinary physical inequality is replaced with a modular one.

The supplied full candidate is a mechanical patch to the actual source pin,
not a claim that every alternative prior proposal coexists in one source tree.
For novelty accounting, the optional branch has already been retired by zq;
its unchanged upstream text is not a claimed residual saving. The full tail
from `cell_val` onward is unchanged. The source file's cardinality `ε≤1`,
physical successor/stride, and cyclic-support statements are therefore not
silently weakened by this pair of proof edits.

`CurrentDummySafety2011.lean` is **not edited**. Its `dummy j = 0`,
`j.val+1<N`, `j.val+s<N`, ordinary nonwrapping conclusion, original source
word, old carry/digits witnesses and updated carry/digits witnesses remain
unchanged. Its checks retain `N=1`, last-cell exclusion, repeated casts,
zero stride, and already-enabled dummy exclusion.

All prior proposed contracts, including deferred, optional, uncompiled and
incompatible alternatives, are assumed available. Generic finite-map/order
rigidity, canonical-cast/modular support interfaces, and carry/normalization
APIs are excluded. So are late zf's common-base quadratic power comparison,
E41's guarded predecessor-power `pow_succ`/`Nat.sub_add_cancel`, coefficient
envelopes/weighted powers, and power-quotient normalization. No change to
`weighted_powers_le`, `nonwrap_of_short`, or `safe_increment_div_bound` is
retained. Incoming finite weighted point-update, Boolean update closure,
optional batches, reset-separated carry locality, and reflected-source `h=0`
specialization are also excluded.

Only the exact budget and injectivity body deletions are claimed after these
contracts are granted. They remain necessary for nonoptional actual position
geometry. A new filename alone is not the novelty argument.

## Portable read-only audit

```text
python /path/to/safety/verify_safety.py
python -O /path/to/safety/verify_safety.py
```

The stdlib-only auditor locates its own directory (or accepts `--root`), reads
bytes, and prints JSON. No writes, subprocesses, network, Git operation, Lean
invocation, or incoming-code execution occur inside it. Shell redirections
save `validation*.json` externally. Checks do not depend on Python `assert`.
Normal and optimized runs pass.

Static checks reconstruct the entire candidate from the two permitted proof
bodies, verify exact combined/isolated diffs and both body-edit orders, bind
hashes/counts, and verify the unchanged support tail and safety/dependency
references. The finite tests provide 141,460 affine points, 2,940 injectivity
pairs, and 5,050 abstract linear `(q,v)` pairs for the retained arithmetic.
Additional tests of the **unchanged baseline safety** cover 25 optional
successor cases, 50 optional stride cases, 250 support sets, and 352 physical
exponent triples. Those supplementary regressions do not restore withdrawn
optional-branch novelty or count as candidate savings. The actual auxiliary
is exhaustive at `k=1`, with selected endpoints at larger exponents. Seven
negative controls retain small-auxiliary, wrong-stride, `ε≤1`, last-cell,
temporal-nowrap and unused-dummy boundaries. None is a Lean proof.

If Lean validation is separately authorized, first rebuild the changed main
module using the pinned toolchain/dependencies, then its focused checks and
downstream actual dummy-safety/controller clients. Do not count checks against
stale `.olean` files as acceptance. Inspect axiom output and resource use.
No such build was attempted here.
