# Internal free-parameter closure and actual schema axiom codes

`ModelCodedBindFree` constructs a fixed represented closing operation in every model of IΣ1. It treats internally coded formulas, including nonstandard codes and arbitrary internal free labels. `ModelCodedClosedSchemaAxioms` uses the result to produce actual internal ZF/ZFC Separation and Replacement axiom membership and literal axiom proof codes. The previous `K.shift = K` restriction is absent from these new constructors.

At traversal depth `d`, `termBindFreeAt` retains an existing bound variable `#z` and sends a free variable `&x` to `#(d+x)`. Function and relation arguments are traversed componentwise. The formula traversal retains all connectives and increases `d` under each quantifier. The term, term-vector and formula graphs are fixed before the arithmetic model `V` is chosen.

For every internal formula code `p`, let `b = bindFreeAt L 0 p` and `m = bv L b`. The checked closing theorem proves:

- `b` is an internally well-formed unbounded formula;
- `shift L b = b`;
- `subst L (fvarVec m) b = p`.

The inverse theorem uses arbitrary internal depths, substitution-vector lengths and vector entries. Its invariant preserves the existing bound slots and opens slot `d+x` to `&x`. Passing under a quantifier changes the vector by the actual `qVec` operation. The quantified induction predicates are Π1, supported by IΣ1. No external finite enumeration of free labels or standardness hypothesis is used.

The closure code is `qqAlls b m`, using the **actual** `bv b`. A larger supplied bound could add vacuous binders and fail the existing exact schema recognizer. The new module gives a fixed Σ1 graph for the total `closeFormulaCode`, proves its well-formedness, and supplies the literal recognizer witnesses `m,b,K`. For Separation and Replacement, the checked raw identity substitutions give the required bound `K ≤ bodyVal K`. This yields the actual `SepR`/`RepR`, then the existing Δ1 classes of ZF and ZFC. The proof code is explicitly `axm (insert p ∅) p`; it is not selected from an assumed existential derivability statement.

The conclusion is a proof of the **universally closed** schema axiom. Specializing an arbitrary internal number `m` of binders back to the open body remains a separate obligation. So do internal interpretation/proof transport, syntax-sensitive Choice proof families and the PA consistency comparison. The external 252-state ConZFC endpoint is unchanged by this checkpoint.

## Verification and dependencies

Lean 4.32.0 was invoked by its real absolute executable, with `-M4096` and `LEAN_NUM_THREADS=1`. No dependency source was changed, fetched or built. The two previously fresh, pinned Foundation `SetTheory.Basic.Misc` and `Axioms` objects from the checked schema prerequisite are reused by exact source/object hashes. The rest are identified cached boundaries, not an attestation of an entire dependency cache. A complete read-only Foundation namespace mirror is needed to avoid partial-root shadowing.

BindFree final run3 freshly checked one source and its audit: **15 probes, 15 callers, standard three axioms only, zero warnings**; source 14.984 s, audit 2.394 s. Its first run failed with ordinary elaboration issues; run2 passed; run3 changed only the descriptive header and is the final byte-bound run. It reuses two local modules, eight named external boundaries (including the two prior fresh objects), and the actual first Omega toolchain object. Thirty input paths were checked before and after.

ClosedSchema first run freshly checked one source and its audit: **13 probes, 13 callers, standard three axioms only, zero warnings**; source 3.423 s, audit 2.355 s. It reuses seven local modules and nine named external boundaries, plus the actual first Omega object. Forty-seven original input paths were checked before and after. Both complete source/audit mathematical reads were independently reviewed by BIC.

The portable guards freeze the final source and audit hashes, check compiler/dependency pins and manifest, verify selected source/object continuity and actual first providers, and check direct Lean imports plus Omega against the pinned compiler sysroot before and after. They accept predecessor evidence/cache paths explicitly. Their prepare-only runs and relocated-provider runs execute no proof commands. Python `-O`, a nonempty output directory, and a fake first Omega provider were rejected for both guards. The successful original proof runs remain distinct from those preflights.

## Reproduction

From the repository root, with existing checked prerequisite objects:

```sh
python -B Logic/Interpretability/ZFCinPA/check_model_coded_bind_free.py \
  --dependency-root /path/to/dependency-checkout \
  --schema-evidence /path/to/schema/verification.json \
  --schema-cache /path/to/schema/cache \
  --output /fresh/external/bind-free

python -B Logic/Interpretability/ZFCinPA/check_model_coded_closed_schema_axioms.py \
  --dependency-root /path/to/dependency-checkout \
  --schema-evidence /path/to/schema/verification.json \
  --schema-cache /path/to/schema/cache \
  --bind-evidence /fresh/external/bind-free/verification.json \
  --bind-cache /fresh/external/bind-free/cache \
  --output /fresh/external/closed-schema
```

Sources and audits default to maintained files. `--source`, `--audit` and the second guard's `--bind-source` allow relocated copies of the same frozen bytes. `--prepare-only` validates inputs and providers without proof compilation. `--library-path` is repeatable and ordered; no checker initializes or builds dependencies. A schema cache produced by the maintained `check_model_coded_schema_axioms.py` supplies the required complete Foundation namespace overlay.

## Next concrete proof obligation

A naive induction on `Provable(closed) → Provable(open)` is not an eligible Σ1/Π1 invariant. A suitable next construction is a **total proof-code iterator** applying a literal one-step universal-specialization constructor. Its invariant carries actual proof-code validity (Δ1) and the remaining-binder formula, with all proof-state values supplied by the total graph. At elapsed `i ≤ m`, the remaining `m-i` binders keep their bound slots while already opened slots map to their original free labels. At `i=m`, the formula is exactly the checked `fvarVec` inverse. This is a proposal, not part of the present checked theorem.
