# Shared binder-aware action

This is an implementation refinement of the existing canonical successor-seeded six-rule calculus. It is not a new arithmetic theory, rule deletion, global minimum, or proof-assistant verification.

## Definition

For a valid term or formula `t`, `action(t,f,d)` protects the first `d` de Bruijn indices. A scalar `i <= d` is unchanged. A larger variable is replaced by `f(i-d,d)`. Numerical zero is always protected. An equation recurses into its two terms at the same depth. Q and D recurse into their matrices at depth `d+1` and `d+2`, respectively. A recursor recurses into counter and initializer at depth `d`, its state-bound body at `d+1`, and invokes the unchanged smart constructor `rec` on the three results. The scalar control additionally recurses into a successor at unchanged depth.

Shift by `k` is the action with `f(i,d)=i+d+k`. Substitution of a list of `m` images uses `f(i,d)=shift(image[i-1],d)` for `i<=m`, and `i+d-m` otherwise.

## Structural equality of operations

For every well-scoped valid numerical term, the new `shift` equals the old `shift_term`, and the new `subst` equals the old `subst_term`. For every valid formula, they equal `shift_formula` and `subst_formula`.

First prove the two shift equalities by structural induction on terms and formulas. Then prove the two substitution equalities by a second structural induction, using the already established shift theorem for arbitrary inserted images. Protected variables agree immediately. The shifted free-variable calculation is `(i-d)+d+k=i+k`. The substituted free-variable calculation selects exactly the same image as the old recursion; the image is lifted by the same depth, and the previously established shift theorem establishes equality of that lift. An unfilled variable becomes `(i-d)+d-m=i-m` in both implementations. Each constructor has exactly its inherited binder increment. Both implementations apply the identical `rec` constructor, so canonical zero-counter body erasure occurs at the same stages, including zero counters first exposed by substitution. The successor case in the scalar control is a direct induction step.

Formula and numerical cases are unambiguous on validated syntax: integers and triple numerical recursors have numerical roots, whereas formula arrays begin with `=`, `Q`, or `D`. No new type convention is used by the public validator.

## Exact accepted certificate relation

The old and new programs have identical JSON drivers, validators, term constructors, rules, contexts, and final-goal tests. The only rule-body changes replace calls to the four old traversal functions by `shift` or `subst`.

Every traversal argument is well formed: the computation branch explicitly validates its three fields; the equality branch validates its template; closure elimination validates its target term; the two binder branches validate the proposed goal and witness before increasing scope. Major formulas and context formulas are well formed by induction on completed derivations. The unchanged hypothesis branch returns only such a context member.

Induct on a finite proof tree. The rule guards agree. When a branch reaches a traversal, the structural equality lemma gives exactly the same raw finite output tree. Thus all subsequent equality comparisons, derived formulas, retained assumptions, and freshness checks agree. Invalid rule shapes and raw input types meet the same unchanged rejection guards. Consequently the new and old programs accept the same finite JSON certificates and compute the same derived formula whenever they succeed, abstracting from finite machine-resource limits. They preserve the same mathematical calculus and therefore its existing bi-interpretation with iPRA.

The proof is an ordinary written implementation argument. The supplied finite tests check actual code paths, capture avoidance, malformed fields, and numerical evaluation; they do not constitute a machine-checked universal theorem.

## Reproduction and provenance

Run `python3 build_shared.py` and `python3 verify_shared.py` in this directory. The `reference/` inputs are unchanged files extracted from `docs/incoming/ipra_canonical_recursors_2026-11-12.zip` at ProveIt commit `6bf83d8765614b0af51b35747e07fb057d6b2f42`. The inherited archive pins its own earlier repository basis. The reference MIT No Attribution license is retained.

The three complete checkers import only Python's `json` and `sys`. Neither the generator nor any test or comparison file is trusted by their command-line acceptance interface.

| Program | Old bytes | New bytes | Old tokens | New tokens | Old AST | New AST | Old gzip-9 | New gzip-9 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Canonical R | 4611 | 4079 | 1338 | 1224 | 1485 | 1378 | 1205 | 1188 |
| Raw R | 4753 | 4221 | 1378 | 1264 | 1532 | 1425 | 1209 | 1191 |
| Scalar I | 4923 | 4313 | 1433 | 1297 | 1595 | 1464 | 1224 | 1200 |

Measurements use CPython 3.12.14, remove actual docstrings, apply `ast.unparse`, and append one LF. Every module is counted in full. Gzip level 9 with timestamp zero is informational only. These are matched transparent-checker improvements; none beats the separate arity-codec compact frontier.

Validation recorded in `verification.json`: 86 inherited named cases, each through old, new, and normalized-new modules in both normal and optimized Python (516 process executions); 480 inherited independent numerical substitution evaluations; 2400 additional old/new traversal comparisons; no mismatch. The new canonical checker accounts for 30 of those cases, 180 process executions, 160 numerical checks, and 800 extra traversal comparisons.
