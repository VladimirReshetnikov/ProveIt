# Units and kernel residues: bounded fifth-iteration review

## Result first

One **minor optional** proof replacement is supplied: derive `Gamma_pos` from
`coprime_Gamma_47`. It saves three physical lines, introduces no helper, and
preserves the theorem statement. It is **not the recommended default** if the
current elementary positivity proof's independence from the literal-kernel
residue/coprimality chain is valuable. No substantial new simplification of
`CurrentKernelResidues2011` survived the assumed-applied screen.

Source pin: `9f35798db4a63c25e435fca14d75931144657d7e`.
Source root: `Computability/DiophantineConsistency/Lean/DiophantineConsistency`.
No upstream source was edited; no source fetch, installation, Lean invocation,
or script from an incoming packet was performed.

## U1 — optional positivity as a consequence of an existing unit fact

Target: `CurrentControllerUnits2011.lean`, `Gamma_pos`, source lines 195–199.

```lean
theorem Gamma_pos (rw n : ℕ) : 0 < Gamma rw n :=
  Nat.pos_of_ne_zero fun hz => by simpa [hz] using coprime_Gamma_47 rw n
```

### Mathematical argument and exact scope

The previously proved fact is `Nat.Coprime (Gamma rw n) 47`. If `Gamma rw n`
were zero, it would imply `Nat.Coprime 0 47`, contrary to `gcd(0,47)=47 ≠ 1`.
A nonzero natural number is positive. No new theorem or helper is needed.

The unchanged statement still quantifies over **independent** `rw n : ℕ`.
Both zero exponents remain included (`dimension 0 = 1`, not zero). The exact
natural `Gamma`, its subtraction, its `radix^977` factor, and the actual
literal `K` are unchanged. There is no orbit, safe mutation, sign or rank-range
claim. The existing `Gamma_cast_rankGamma` remains untouched. The known
`q=1` degeneracy is not weakened.

This uses the natural-number domain critically: nonzero coprime integers can
be negative. It uses the nontrivial modulus 47 critically: `gcd(0,1)=1` would
not imply positivity. It does not require a new explicit hypothesis because
the exact coprimality theorem already holds for every pair of parameters.

### Honest cost and dependency tradeoff

| Item | Before | After | Net |
|---|---:|---:|---:|
| Full source file physical lines | 201 | 198 | −3 |
| Replaced declaration physical lines | 5 | 2 | −3 |
| New helpers/imports | 0 | 0 | 0 |
| Public statements changed | 0 | 0 | 0 |

The terse expression accounts for part of the three-line difference; an
expanded proof is `apply Nat.pos_of_ne_zero; intro hz; simpa [hz] using ...`,
three tactic steps rather than the existing four proof-body lines. The real
logical change is consequence reuse, not the line wrapping.

The old proof depends only on `q_gt_one`, arithmetic positivity, and the
positive radix. The proposed proof additionally depends on
`coprime_Gamma_47` → `quadratic_mod_47`, `coupling_mod_47` → unconditional
`CurrentKernelResidues2011.Hs_mod_47` → actual `K_mod_47`/`K_cast_47` and the
physical selector certificates. These are already imported and proved earlier
in the same module, but this still creates an additional logical dependency.
In particular a future kernel recalibration could invalidate the modular unit
fact while elementary positivity still holds. **Retaining the original proof
is reasonable and preferred when that separation is intentional.**

No runtime saving, compilation speedup, reduced trust base, or changed axiom
set is claimed. The exact axiom footprint has not been printed because Lean
execution was not authorized. Kernel-checked numerical certificates in the
source are dependency evidence, not validations rerun here.

### Novelty boundary

The round-four ledger and the baseline review of inherited and fresh
corpus screen found no earlier positivity-from-coprimality proposal for this
new exact client. The nearest old interfaces are integer-unit sign extraction,
generic cast/residue normalization, and scalar `C+qF` rank-order comparison.
None removes this particular second proof of positive natural `Gamma`.
Nevertheless this is routine consequence reuse, **not** a new positivity,
unit, rank comparison or modular arithmetic abstraction. All older proposals
remain assumed applied whether or not present in maintained source.

### Files and verification

- `baseline/CurrentControllerUnits2011.lean`: exact source snapshot.
- `candidates/CurrentControllerUnits2011.lean`: complete optional replacement.
- `patches/gamma_pos_from_coprime.patch`: exact patch against the pinned path.
- `provenance.json`: hashes, source pin, line counts and validation boundary.
- `checks/check_units.py`: portable, read-only standard-library checks.
- `checks/check_result.json`: captured output from the script.

The script checks hashes, exact single-proof-only replacement, unchanged
statement/imports, exact diff, no new placeholder/axiom, helper-inclusive line
counts, declaration dependency direction, and the simple gcd implication. It
also checks 147 modular combinations `(rw,n) ∈ {0,…,6}²` for each of the three
moduli, using the *supplied public calibration residues*. This is deliberately
not independent evaluation of the 941 selector rows or the literal kernel.
The fixed Gamma residues in those checks are 14 mod 47, 232 mod 2011, and 93846
mod 120199. These smoke checks do not prove the universally quantified Lean
statement or validate elaboration; the mathematical zero contradiction does.

Run from any directory:

```text
python3 /path/to/units/checks/check_units.py
```

Result: 319 checks and 147 finite modular cases passed. Lean elaboration,
kernel validation and axiom audit were **not run**. No operation was denied or
left with an uncertain execution result.

## Rejected/non-promoted directions

1. **Kernel finite chunk dispatch and list assembly.** Already proposed;
   deliberately not repackaged. The 59 checked blocks per modulus and their
   append assembly are not credited as new savings.
2. **Selector signal-mass aggregation.** Already assumed applied. No change
   proposed to the physical selector semantics or weighted sum interface.
3. **Modular cast/rewrite helper reuse.** `mod_of_cast`, modulus transport,
   coprimality from nonzero prime residue, and Hs wrapper cleanup are not
   claimed as new abstractions; the round-four Hs inline recommendation is
   already excluded. The kernel Hs residues are now unconditional in current
   source, not still pending hypotheses.
4. **Order-free fixed-point exponent iteration.** One can prove
   `B^auxiliary = B` in each modulus and iterate to derive
   `B^(auxiliary^n) = B`, avoiding exact-order reasoning at the point of use.
   The generic helper plus three clients largely erases the source savings;
   its new finite modular power checks also replace existing small-order
   certificates. No candidate, patch or performance claim is supplied.
5. **Composite-modulus unit proof.** Direct fixed-prime factor assembly is
   already only a few lines. Introducing a combined residue/CRT interface
   would add infrastructure whose reduction was not established. No candidate
   or unearned savings is supplied.
6. **Exact new rank API.** Existing `Gamma_cast_rankGamma` is already a short
   cast normalization proof. General rank-order factorization through `C+qF`
   was proposed in the late663 manuscript and remains excluded.

## Final exclusion refresh

The bounded closure through `91dce223c` adds the zg/zi review documented in
`late91_review.md` and its hash-bound JSON. No collision with U1 or the other
retained families was found in those manuscripts or their optional/prototype
mechanisms. The candidate and source hashes are unchanged.
