# Current iPRA draft frontier audit

Snapshot: `VladimirReshetnikov/ProveIt`, commit
`0300a290bedee5019c974291850b798378438b2e`.
Audit environment: CPython 3.12.14. No source file in the baseline corpus was
modified. The audit parses source rather than running source while measuring.

## Scope and measurement

The 16 ZIP archives currently in `docs/drafts` contain 22 distinct ZIP payloads
when embedded historical archives are included. After deduplicating archive
payloads, there are 516 Python member occurrences and 297 distinct Python
source hashes. The inventory filter identifies 262 occurrences / 134 distinct
hashes with an explicit public `ACCEPT` driver and standard input use. This
filter is an inventory aid, not an automatic correctness certificate. All
minimum-attaining candidates below were manually inspected, together with
their package descriptions.

The published comparison convention removes genuine module/function/class
docstrings, applies `ast.unparse` to the whole module, adds one final newline,
and counts normalized UTF-8 bytes, significant lexical tokens, and AST nodes.
Comments, indentation tokens and newlines are excluded from token count. Input
parsing, opening, rule checking, rejection and public verdict drivers remain
charged. Python and the standard JSON implementation are shared host costs.

The supplementary gzip metrics use exactly
`gzip.compress(source_bytes, compresslevel=9, mtime=0)`. Both raw-file and
normalized-file sizes are recorded; the gzip wrapper is included. These
compressed sizes are descriptive measurements, not optimization objectives.

## Current coordinate minima

Different complete programs attain the coordinate minima. These are attained
upper bounds on an unknown optimal checker size, not proven lower bounds.

| Coordinate | Minimum | Attaining current archive/member |
|---|---:|---|
| Normalized bytes | 672 | `ipra_counter_congruence_2026-11-10.zip` / `ancillary/zero_product.py` |
| Normalized tokens | 277 | `ipra_constructed_computation_2026-11-10.zip` / `code/checker_explicit.py`; also two matched source profiles in scalar-successor references |
| AST nodes | 311 | `ipra_transient_seed_2026-11-10.zip` / `code/checker_structure.py` |
| Raw source bytes | 628 | `ipra_local_rewriting_2026-11-10.zip` / `code/kernel_scalar_boxed.py`; identical copy in flat-computation references |
| Raw-source gzip-9 bytes (FYI) | 381 | `ipra_local_rewriting_2026-11-10.zip` / `code/kernel_balanced.py` |
| Normalized-source gzip-9 bytes (FYI) | 390 | `ipra_transient_seed_2026-11-10.zip` / `code/checker_joint.py` |

Thus a strict simultaneous improvement under the inherited normalized
convention must have fewer than 672 bytes, 277 significant tokens and 311 AST
nodes in one complete program. Improving only the old per-report envelopes
is insufficient: several reports were written against earlier snapshots.
Raw-source comparison has a different incumbent and cannot be substituted
for normalized comparison without saying so.

## Important qualifications

1. **References and ancillary programs count.** The 672-byte leader is not the
   main counter-congruence checker. Its package explicitly says it is a
   standalone implementation of the inherited generated-assumptions theory.
   Its improvement is Python source spelling, not the new counter-congruence
   arithmetic proposal. Omitting `ancillary/` would give the wrong frontier.
2. **The 672-byte predicate is valid for the public JSON contract.** It replaces
   `isinstance(a, list)` by `a * 0 == []`. Exact JSON-decoded lists satisfy it;
   numbers, booleans and strings do not; dictionaries and null reject earlier
   than in the original, whose subsequent numerical comparison also rejects.
   There is no inner exception recovery in this opener. This preserves
   successful values and acceptance under the declared runtime contract,
   modulo ordinary finite-resource qualifications.
3. **The AST leader is runtime-dependent.** Its exception-based opener permits
   empty strings and some empty-key dictionaries as disclosed zero/successor
   aliases. Nonempty strings recursively split into themselves until Python's
   recursion limit raises. This is a complete terminating public CPython
   program on such malformed cases, but not a structurally terminating parser
   over arbitrary JSON under an ideal unbounded stack. The 381-byte compressed
   winner uses the same kind of permissive opening. Such profiles should not
   silently be compared with a stricter total-parser contract.
4. **No proof-assistant certification is supplied for the universal claims.**
   The inherited packages provide written arguments, finite arithmetic
   diagnostics and certificate suites. I did not independently formalize
   their universal soundness, completeness or bi-interpretability arguments.
   No new decisive mathematical defect was established in this scoped audit.
5. **Do not confuse syntax changes with a breakthrough.** Several source
   reductions (import spelling, list-type predicate, moving a conditional
   expression, inverting a guard) preserve the same arithmetic theory. They
   improve an implementation record but do not alone justify a significant
   mathematical novelty claim.

## Independent replay

After reading the 672-byte program, I replayed its 28 supplied witness cases
and three malformed payloads with an independent subprocess runner, both
normally and with `-O`. All 62 checks passed: 28 acceptance cases and 34
rejection cases, including the optimization duplicate. This corroborates its
claimed finite test behavior; it does not prove the universal metatheory.
`byte_leader_validation.json` contains the per-case records.

## Files

- `audit_frontier.py`: reproducible read-only archive traversal and metrics.
- `frontier_metrics.json`: full inventory, provenance hashes, minima and aliases.
- `checker_metrics.csv`: all driver-filtered checker occurrences.
- `byte_leader_validation.json`: independent replay outcomes.

The audit script expects the pinned archives at `../ProveIt/docs/drafts`.
