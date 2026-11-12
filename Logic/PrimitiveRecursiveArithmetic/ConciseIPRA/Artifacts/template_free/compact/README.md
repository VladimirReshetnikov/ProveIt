# Compact forward implementations: supplementary evidence

This directory supplements the main report's strictly parsed, tagged proof
checker. It contains a small forward implementation of global replacement,
an independently produced certificate suite, and a forward implementation of
the existing one-sided crossed replacement rule for comparison.

**These programs do not beat the repository's 520-byte compact record.**
They use the inherited raw arity representation, including administrative
aliases, and do not implement the main checker's strict public syntax
validator. Their source sizes must not be attributed to that stricter
interface. The mathematical equivalence theorem is in the main report;
these execution results are finite implementation evidence, not a Lean or
Rocq verification of either Python module.

## Reproduce

From the extracted archive's root, run:

```sh
python3 compact/verify.py
```

The script uses only the Python standard library. All paths are relative to
the script's own directory, so it also works when invoked from another
working directory. It regenerates `cases.json`, `results.json`,
`metrics.json`, the two exact-source gzip files, and the control's fixtures
and results. It runs each certificate in a separate normal interpreter and
again with `python -O`.

The delivered result is **PASS**:

- 50 process expectations for the global-replacement checker: 25 cases in
  two interpreter modes.
- 34 process expectations for the forward crossed-rule control: 17 cases
  in two modes.
- Two deliberate-mutant controls establishing that a shared-sentinel bug
  accepts the supplied closed false proof. The corrected checker rejects
  that same proof in both modes. The defective program is created only in
  a temporary directory and is not a delivered checker.

The main suite includes both computation schemas; all-occurrence replacement;
rejection of an attempted primitive selective replacement; selective
congruence derived by an oversized alias despite accidental passive
occurrences; transport with both endpoints dependent on the replaced term;
literal-zero sources; replacement beneath two iterator binders; and scope
controls. Its positive DE test actually uses the fresh witness in QE and an
arithmetic computation before removing it from the conclusion.

## Input and acceptance contract

`checker.py` reads one JSON value of the form `[proof, goal]` from standard
input. Acceptance means normal exit and **exactly** `ACCEPT` followed by a
newline on standard output. An exception, other output, or an empty output
is rejection. A failed final goal comparison can exit normally without
printing, so an exit-code-only caller would be incorrect.

A proof is either an integer indexing the current reusable context or a
pair `[major_proof, data]`. The initial context contains the administrative
truth `[]`, interpreted as the derivable equation `0 = 0`. Canonical
certificates use nonnegative context indices; the raw Python indexing
behavior also permits harmless negative references to existing assumptions.

The major proof is synthesized first. Its formula determines the rule:

| Major | Data | Result or obligation |
|---|---|---|
| Equation `[s,t]` | A minor proof of `[u,v]` | Synthesize `[v, R_s^t(u)]`. No template, path, or mask is supplied. |
| Closure `[B,B,B]` | `[minor_proof, target]` | Require the minor to prove `B(0)`; synthesize `B(target)`. |
| Paired binder `[B]` | A continuation proof | Give the continuation the closure at a fresh witness; rescope its result before returning it. |
| Administrative truth `[]` | `[counter, initializer, update]`, with truthy initializer | Synthesize the corresponding base or successor computation equation. |
| Administrative truth `[]` | `[paired_goal, 0, [witness, premise_proof]]` | Check the witness-sensitive introduction rule and synthesize the paired goal. |

For a computation packet, a falsy counter selects the base case, while a
truthy counter supplies the predecessor of a constructed successor. Thus
the canonical compact interface omits literal-zero initializers and a
literal-zero successor predecessor. The uniform construction below avoids
these omissions in the new congruence compiler.

For introduction, a literal equation matrix with the literal witness `0`
uses its progressive premise. Every other case uses its zero premise. The
conclusion is tested at a fresh successor parameter. The checker derives
the same native theory through the translations discussed in the report;
it does not introduce induction on an arbitrary quantified matrix.

The numerical and formula representation is inherited from the ConciseIPRA
arity codec:

- Numerical `0` is the canonical scalar zero, a unary array is successor,
  and a ternary numerical array is an initialized scalar iterator.
- Formula arities one, two, and three encode `D`, equality, and `Q`.
  A canonical `Q` has three equal children.
- Numerical root depth is three. Each protected numerical slot occupies
  two coordinates. The opening traversal adds `5 - arity` at each array.
- Successor adds two dummy zero slots. An iterator adds a slot that is
  dummy in its counter and initializer and genuine in its update.
  Negative integers name retained numerical parameters.

Raw administrative aliases retain their inherited meanings. In particular,
empty and surplus formula arrays can denote truth; they are not additional
logical connectives. The supplied producers use canonical numerical syntax
and the documented administrative truth. This supplement does not claim
that all semantically equivalent raw aliases have interchangeable raw
certificates.

## Why the oversized alias works

Let `H[-]` be a finite term context, including its passive parameters. Pick
a closed numeral `N` with more syntax-tree nodes than `H[-]`. In the
unrestricted mathematical calculus, `K = I(0,s;u.N)` satisfies `K = s`.

The actual compact certificate producer uses the uniform variant

```text
C_s = I(2,1;u.s)
K   = I(0,C_s;u.N)
```

An allowed successor computation proves `C_s = s`, and an allowed base
computation proves `K = C_s`. Root transitivity gives `K = s`, including
when `s` is the literal zero. From `s = t`, it also gives `K = t`.

Since `K` is larger than the whole context, it cannot occur in a passive
part of that context. A proper subterm of an inserted `K` is smaller than
`K`, and an ancestor containing it is larger. Consequently, top-down
replacement of `K` in `H[K]` changes exactly the designated copies:

```text
R_K^s(H[K]) = H[s]
R_K^t(H[K]) = H[t]
```

Applying the primitive rule to reflexivity of `H[K]` gives a common left
side for `H[s]` and `H[t]`; joining at that left side gives their equality.
Lifting under a binder preserves tree size, so this argument is
capture-safe. It requires no existential naming or numerical induction.
`oversized_alias_proof.txt` gives the root equality algebra and the
subsequent two-sided transport construction in detail.

## Scope and sentinel details

Three small implementation details are significant:

1. The missing-image default is `None`, while the replacement-source
   default is the unforgeable checker function `c`. Using `c` for both
   makes missing-image validation match the replacement source instead of
   raising an error. Two escaped witnesses then collapse to that same
   function object. The included attack turns that defect into acceptance
   of the closed false equation `0 = S(0)`.
2. The replacement-source parameter is keyword-only. This preserves the
   argument-unpacking check that forces a nontrivial introduction goal to
   be a unary `D` formula. Adding an ordinary fourth positional parameter
   would weaken that check.
3. DE decreases the scope floor before forming the witness export and
   checking its continuation. It restores the old floor before validating
   the synthesized conclusion. The meaningful positive DE regression and
   negative escaping-witness controls check both sides of this order.

Inserted replacement targets are returned without being visited again.
This is essential when the target contains the source. The implementation
also resets the replacement source when the ordinary opening traversal
validates a substitution image.

## Fair size accounting

Measurements use CPython 3.12.14 and zlib 1.3.2. Whole modules are normalized
with `ast.unparse(ast.parse(source))` plus one final newline. Token counts
exclude layout, comments, encoding, and end markers. AST counts include
every node. Gzip uses level nine and timestamp zero; it is informational.

| Complete forward module | Normalized bytes | Tokens | AST nodes | Normalized gzip-9 | Exact-source gzip-9 |
|---|---:|---:|---:|---:|---:|
| Global replacement, `checker.py` | 865 | 397 | 464 | 437 | 435 |
| Crossed-rule control, `control/forward_x.py` | 830 | 384 | 448 | 414 | 411 |

The exact sources contain 862 and 827 bytes respectively. The `.py.gz`
files compress those exact delivered sources. `metrics.json` records
runtime versions and both raw and normalized SHA-256 identities.

These two forward implementations use different certificate layouts, so
this is **not a matched ablation measuring only one rule change**. They are
also distinct from the main report's strictly parsed tagged checker and
its matched control. The code here demonstrates an implementation and
finite certificates, while recording its extra source cost candidly.

## Provenance

The shared arity traversal, administrative aliases, scalar arithmetic,
local scope discipline, and witness-sensitive introduction come from the
existing ConciseIPRA development. Relevant sources include
`Research/certified_zero/reference/inherited_arity_checker.tex` and
`Research/source_dispatch/code/checker_bytes.py` in the source repository.
The two forward modules are same-session implementations built for this
comparison; the crossed rule itself is an existing proposal. Global
replacement and its oversized-alias compiler are the present construction.
The main report and frozen reference material record the repository
snapshot and attribution. Neither checker imports those references, the
producer, a theorem database, or another proof checker.
