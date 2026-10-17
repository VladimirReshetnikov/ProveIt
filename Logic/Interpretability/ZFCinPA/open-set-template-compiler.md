# Compile templates at arbitrary internal set predicates

The [97-line client](Lean/ZFCinPA/OpenSetTemplateCompiler.lean) instantiates the
[finite-buffer compiler](buffered-template-proof-compiler.md) with the existing
set-language placeholder translation. Each placeholder can now be any internal
formula of its declared arity, with arbitrary free parameters. No shift-fixedness
assumption is required.

At buffer b, the client shifts each placeholder b times. The checked family law
translates a shifted source formula at buffer b+1 to the shift of its translation
at b. The corresponding free-variable law follows from this and substitution.
These laws provide exactly the compiler's universal-introduction and SHIFT cases.
The compiler returns an actual internal proof of the unbuffered conclusion.

The source theory remains arbitrary. For every source axiom and buffer, the
caller must supply an actual target proof of its translation. This permits the
proved open Separation and Replacement instances to serve as callbacks, but
this client does not yet assemble those callbacks or prove Collection G.

The [audit](Lean/ZFCinPA/OpenSetTemplateCompilerAudit.lean) has eight axiom probes
and eight callers, including a binary predicate with no restrictions on its
internal free parameters. All reports use standard Lean axioms only. The two
unchanged project precursors, `TypedTemplateProofCompiler` and `SetPlaceholders`,
were freshly checked before the client; no previously unattested project object
was substituted for either source. Their times were 3.517s and 4.214s, followed
by 2.217s for the client and 2.005s for its audit.

Exactly two harmless style warnings remain: an unused section instance in the
older compiler and an implicitly used buffer binder in the new client. The
successful bytes are preserved. An earlier attempt failed only because six
record-field lambdas omitted their implicit arity binders. That attempt and
the exact repair are retained in the
[history](results/open-set-template-compiler-history.json).

The [successful record](results/open-set-template-compiler-verification.json)
checks 56 inputs, thirteen reused project modules, seven direct external
source/object boundaries, the actual first Init/Omega providers, and all three
fresh objects. The existing Foundation namespace is reused without a complete
rebuild. There is no dependency build or download.

```bash
python Logic/Interpretability/ZFCinPA/check_open_set_template_compiler.py --output /tmp/open-set-template-replay
```

The runner supports explicit repository, dependency, source/audit, parent,
cache, namespace, compiler, and library paths. Its maintained copy equals the
executed guard. Packaging adds an unbuilt default preparation and
[independent review](results/open-set-template-compiler-review.json), with no
successful-proof replay or extra rejection controls. Collection, the actual
numerical G clause, and the internal PA consistency comparison remain open.
