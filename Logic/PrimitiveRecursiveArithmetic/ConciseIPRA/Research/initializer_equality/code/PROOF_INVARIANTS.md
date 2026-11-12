# Initializer equality: implementation and proof translations

All final programs use **ordinary, uncrossed replacement**. The selected Seed rule concludes `C(n,t,h)=r` from `s=t` and `C(n,s,h)=r`. Its matched general-context control concludes `f(t)=r` from `s=t` and `f(s)=r`. Both use ordinary Q elimination. Crossed precursor experiments are not part of the delivered comparison.

## Canonical syntax and the fixed slot

The numerical grammar is `0`, variables, successor, and scalar iterators whose counter is not syntactically zero. The smart constructor `C(n,a,h)` returns `a` at a literal-zero counter and otherwise the iterator node. Capture-avoiding action transforms children before applying this constructor. In particular, substituting into a nested counter can collapse its inner iterator and then collapse the outer iterator. Only zero computation is built into syntax; successor computation remains an explicit rule.

If the minor equation is `b=r`, every instance of Seed is recognized directly from the two proved equations. The zero-counter case is `b=s`. In the nonzero-counter case `b` is a triple iterator whose middle child is `s`. Its counter and body are recovered from the first and third children. They may contain ambient parameters equal to `s` as a matter of arithmetic; they are not rewritten. In particular, this is replacement at one fixed syntactic field, not textual replacement of every equal-looking subtree.

No two branches compete on finite terms. If an iterator both equalled `s` and had initializer `s`, then a finite tree would contain itself as a proper subtree. JSON produces finite acyclic trees, so this cannot occur.

## The ordinary mathematical equivalence

Write `J(a)=I(1,a;u.u)`. Successor computation and zero canonicalization give `J(a)=a`. Use it as both premises of Seed at counter zero to get `a=a`. Given `s=t`, use it as major and `s=s` as minor at counter zero to obtain symmetry `t=s`. Given `a=b` and `b=c`, first derive `b=a`, then replace the left `b` of `b=c` to obtain `a=c`. Thus ordinary equality algebra is available without induction or any logical binder rule.

For an arbitrary numerical template `f(u)` and a proof `P:s=t`, define

- `A_s=I(1,s;u.f(u))`, `A_t=I(1,t;u.f(u))`;
- computation gives `A_s=f(s)`;
- Seed at counter one using P gives `A_t=f(s)`;
- a second computation gives `A_t=f(t)`;
- Seed at counter zero, taking `A_t=f(s)` as major and `A_t=f(t)` as minor, gives `f(s)=f(t)`.

This congruence proof contains P once and adds exactly four inference nodes. A further counter-zero Seed step with minor `f(s)=r` gives `f(t)=r`, recovering the control's general-context rule. It changes neither proof scope nor assumptions. Conversely each Seed instance is one general-context instance, with template `u` in the root case and `I(n,u;v.h)` in the initializer case, with the necessary de Bruijn lifts.

The maps are identity maps on public terms, formulas, and contexts; they translate only proof nodes. Thus they prove exact equality of the two consequence relations. Their existing zero-canonical scalar bi-interpretation with iPRA transfers to the restricted rule. These local arguments do not by themselves replace the separately supplied raw/canonical arithmetic bridge or its body-extensionality proof.

## The two executable proof translations

`translate.py` is untrusted producer code. `to_seed` validates a control proof and replaces each general equality node by the five-node construction just described: four nodes recover congruence, and one replaces the minor's left endpoint. Each translated major and minor occurs once. Other nodes retain their inference kind and recursively translate their subproofs in exactly the same extended contexts and scopes.

Consequently a proof with N inference nodes translates to at most 5N inference nodes. This is not a linear bound on serialized JSON size. Recovered endpoints and templates may be large terms and are inserted in the two new computation packets.

`to_general` recovers the identity context or the single initializer context from the two inferred premises. It replaces each Seed node by one general equality node. Under an iterator body, the state binder is protected while old ambient variables are shifted to make room for the context variable. Thus this direction preserves the number of inference nodes. Both translations preserve the exact concluded canonical formula and all assumptions; both round trips have the same sequent. The translation algorithms are not part of either acceptance module.

## Scoped-derivation invariant

For a well-scoped input context at scope n, a successful call of `derive` returns a formula of that scope. Prove this by induction on successful recursive derivations.

The hypothesis branch chooses a context member. The computation branch explicitly validates its three numerical fields. Q elimination validates its target before instantiation. D elimination validates the proposed conclusion at the old scope, shifts the old context, and uses the newly bound witness only in the extended branch. D introduction validates its witness before opening its fresh induction/case variable. The shared substitution action preserves scopes and canonicality by its structural recursion and unchanged smart constructor.

In the general equality branch, the numerical template is validated at scope n+1 and both premises have scoped equation endpoints. Substitution produces scoped terms. In the Seed root case, the result contains the major's target and the minor's right endpoint, both already scoped. In its iterator case, the verified minor's counter and body remain unchanged, and its initializer is replaced by another term of the same scope. Its nonliteral-zero counter remains nonliteral zero. Therefore the direct updated triple is scoped and canonical.

The public driver starts with the empty context and scope zero. Hence the invariant applies throughout every accepted public certificate.

## Why arity unpacking is safe

A derived formula is an Eq array of length three or a Q/D array of length two. Thus unpacking it as `_,source,target` succeeds exactly in the equation case. This omits a redundant explicit root-tag test; it does not admit another formula type. The same optimization is used in the matched control and selected Seed checker.

For Seed's non-root minor, the left term is a validated integer, a unary successor array, or a triple iterator array. Accessing `left[1]` fails on the first two kinds. If the initializer comparison succeeds, the term is necessarily the correctly scoped triple already described. The explicit-shape checker spells out these cases. The selected checker relies on the invariant and the unchanged contract that all exceptions reject. These variants therefore accept the same finite JSON certificate language, apart from possible finite-resource thresholds. External Python calls to `derive` with an invalid context are outside its stated precondition and the JSON interface.

## Measurements and their limits

The final uncrossed complete modules are measured under CPython 3.12.14 after removing actual docstrings, applying `ast.unparse`, and adding one LF. Significant tokens omit comments and layout tokens; AST counts use `ast.walk`. Gzip level 9 has timestamp zero and is informational.

| Complete module | Normalized bytes | Tokens | AST nodes | Gzip-9 |
|---|---:|---:|---:|---:|
| General context, matched invariant control | 4029 | 1202 | 1360 | 1173 |
| Seed, selected invariant checker | 3979 | 1192 | 1347 | 1175 |
| Seed, explicit shape checks | 4156 | 1236 | 1404 | 1226 |

The matched mathematical restriction saves 50 bytes (1.2410%), 10 tokens, and 13 AST nodes; gzip grows by 2 bytes. The comparison uses the same shared action and the same premise-unpacking invariant on both sides. `source_diff.patch` shows the complete source difference. The sole mathematical difference is the equality rule. This is a modest matched implementation gain and a simpler primitive inference interface. It does not beat the separate 516-byte arity-codec record, and it is not an absolute minimality theorem.

## Executed checks

`results.json` records 600 complete CLI executions: 30 positive cases for each of three programs; 10 negative control cases; and 25 negative cases for each Seed version. Each case is run in readable and normalized source, under normal and optimized Python. There were no mismatches.

The positive cases include nested numerical templates, absent and repeated template variables, binding under iterator states, literal-zero major sources, nested zero counters exposed by substitution, ordinary Q elimination, a genuinely used equation-induction hypothesis, a nonliteral zero witness, fresh existential witnesses reused by later introductions, and Seed application at counters other than one. All 30 closed proofs translate both ways with unchanged goals. An additional open proof has the same ambient parameter in the changed initializer, unchanged counter, and unchanged body; both translations preserve its exact conclusion.

There are also 180 comparisons with an independent natural-number evaluator, plus direct checks of nested counter normalization, state-binder capture avoidance, and capture across nested D/Q binders. Negative cases exercise missing or wrong inference fields, rejected raw types, out-of-scope variables/templates/witnesses, escaped eigenparameters, non-equational premises, invalid initializer positions, and false goals.

These are executable controls, not a Lean/Rocq verification of the new theory or of Python. The universal claims above are written proofs. No further optional testing was used after resolving the identified input-shape and capture risks.

## Provenance and reproduction

This directory is self-contained. `build.py` reads the copied shared scalar control in `reference/scalar_shared.py`; `test_seed.py` imports only the local checkers and translation producer. `python3 build.py` followed by `python3 test_seed.py` regenerates the modules, named certificates, normalized and gzip copies, measurements, and test receipts. The reference license is retained.

The shared scalar control derives from the strict scalar checker in `docs/incoming/ipra_canonical_recursors_2026-11-12.zip` at ProveIt commit `6bf83d8765614b0af51b35747e07fb057d6b2f42`. Its separate shared-action refinement and exact old/new comparison are documented in the companion `shared_traversal` directory. That common refactoring is not attributed to the new Seed rule when reporting the 50-byte matched gain.
