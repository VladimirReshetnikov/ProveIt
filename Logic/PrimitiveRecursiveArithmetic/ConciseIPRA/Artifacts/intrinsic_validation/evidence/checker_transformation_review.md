# Intrinsic leaf checking: candidate implementation audit

## Recommended integer-forcing candidate

File: `work/benchmark/candidates/proper_compareforce.py`

Measured whole-module coordinates, CPython 3.12.14, after `ast.unparse` plus one LF:

- 316 significant tokens;
- 360 AST nodes;
- 591 normalized UTF-8 bytes.

The source is standalone apart from the standard-library JSON reader. No external table, compiler, schema, decoder implementation, or generated source is loaded by the checker. The three positional arguments of the opener remain unchanged, so an equation cannot enter the unary introduction branch through excess arguments.

The matched upstream source is `code/proper_bytes.py` inside the current incoming archive `ipra_exact_bindings_2026-11-13.zip`, at repository commit `fc05b10f0e03f22edbfdde9298a29fb2fee5dc59`. It measures 330/383/627. The entire exact-public-grammar family's independent envelope is 321/361/627. Thus this one candidate is smaller in every coordinate of that family. It is not below the compact promise-domain envelope or the weaker sorted grammar envelope.

## Source transformations

1. Delete the whole-input character whitelist. Read the input by `q = load(open(0)).pop`.
2. Recognize lists with `a * 0 == []`, replacing `a * 0 != 0`.
3. Force each traversed scalar to support bitwise OR by comparing `k <= a | 0 < d`, replacing `k <= a < d`.
4. Replace `s and [s] or 1` by `[s] if s else 1`. The middle operand is a nonempty list whenever it is selected, so the values and evaluation effects agree.
5. Replace `s and r[:2] or [t] * 3` by `r[:2] if s else [t] * 3`. On a successful four-element list unpack, the slice has exactly two elements and is truthy. Non-list consumed packets cannot invalidate the soundness argument: dictionaries either fail slicing in both versions or select the false branch, and nonempty strings fail intrinsic traversal. The arithmetic proof compiler emits only four-element lists.
6. Replace the term-position child increment `2 * (j == 2)` by `j & 2`. At semantically meaningful term constructors, the only cases are unary successor (j=0) and ternary iteration (j=0,1,2), where these expressions agree. At other arities the raw term reading is constant zero, so its children are annotations. The formula-position increment remains `5 - len(a)`. Both updates obey `delta(d+2,r,j)=delta(d,r,j)+2`, preserving exposure.
7. Use `from json import load` instead of `import json`, removing two AST nodes without changing the reader.

The eager two-element tuple used for the goal selector is deliberately retained in this recommended file. Both `i(t,s)` and `i(t,u)` are still evaluated at the same stage as in the source control. A separate smaller sorted candidate prunes an unused check with a conditional; it is not part of this recommendation.

## Intrinsic alphabet lemma

Let an opener call return successfully. Every source scalar that it visits must be a Python integer or Boolean. For JSON-decoded data, lists are exactly the values satisfying `a * 0 == []`: multiplying a string by zero yields an empty string, while multiplication of a mapping or null fails. For a non-list branch, `a | 0` rejects floats (integral or fractional, finite or infinite), strings, null, and mappings. It accepts integers and Booleans; Booleans have their ordinary 0/1 numerical meaning. Since recursive reconstruction visits every child of every source list, every successfully traversed source tree is an integer/Boolean/list tree.

This lemma is local: an image argument need not be visited when no hole uses it, and an unused prefix of the input document need not be visited. Such data do not become trusted formulas merely because they are present in the certificate.

The first opener call uses k=0. In that call the sorted public checks are enabled. Even scalar codes, zero, negative codes, out-of-scope codes, invalid constructor arities, and formula-position scalars reject. Therefore a successful public goal is exactly an actual-binder canonical Eq/D tree, allowing `true` as an alias for the canonical zero code 1. Public `false` rejects. All accepted public goals can be canonically decoded by replacing true with 1; no unvalidated numerical code is exported.

Rejecting Booleans by exact Python type would cost additional source; it is unnecessary for arithmetic soundness. The Boolean alias must nevertheless be stated in the input specification. This is a fully defined nontraditional encoding, not an external type promise.

## Remaining universal-input proof obligation

The intrinsic alphabet lemma directly handles all arguments successfully scanned by the opener. Raw packet fields used only in the terminal computation candidate may be unscanned. If that candidate is equal to the typed scanned goal, Python structural equality forces matching list shape and equal numeric leaves. Thus a numerically equal Boolean or integral-float annotation denotes the same native term; a fractional number, string, null, or mapping cannot replace a canonical numeric/list leaf in such a match. The zero computation rule ignores its body; the successor case explicitly opens the body, where the intrinsic alphabet lemma applies.

For inferred equality/closure elimination, the major proof is checked and the two template instances are scanned. An unvisited image has no active occurrence, so an arbitrary numerical image can be chosen in the semantic reconstruction. Retained context entries are opener outputs, hence are typed modulo Boolean aliases. These observations allow the upstream raw-reading/opening/freshness proof to be applied inductively to a successful call tree. The incoming_audit and mathematics agents are independently auditing this universal-input argument and testing the implementation. Finite regressions alone are not the proof.

## Inherited mathematics and limits

The ordinary theory and its eight-rule native core remain unchanged. The current source report's Sections 5.3-5.5 provide the integer/list raw interpretation, opening/exposure/freshness lemmas, proof-call-tree cases, and native proof compiler. The new contribution is intrinsic alphabet checking and the harmless child-index update, not deletion of an arithmetic or logical axiom. Full iPRA bi-interpretability, both formula round trips, actual equality, whole numerical domains, and identity numerical comparison graphs are inherited through that native core.

This measured improvement addresses the fully validated actual-binding interface family. It does not meet the user's stronger requested comparison with all compact minima. No universal simplicity lower bound, new arithmetic axiomatization, or formal Lean/Rocq verification of this Python implementation is claimed.
