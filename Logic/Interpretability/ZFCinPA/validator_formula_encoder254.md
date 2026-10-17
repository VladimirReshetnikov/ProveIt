# Represented formula encoder

`ValidatorFormulaEncoder254` defines one fixed Sigma1 graph before the
arithmetic model. In every model of IΣ1 it is total and Delta1-definable on
all internal source/depth inputs. Its recursion uses Foundation's internal
`Language.TermRec` and depth-changing `UformulaRec1`, rather than recursion
on an ordinary Lean formula datatype.

On typed set-language syntax at internal depth m, free variable j receives
label 2*j+1 and bound variable i<m receives label 2*(m-i). A binder receives
label 2*(m+1), and its body is encoded at depth m+1. Genuine variable labels
are positive, leaving label 0 for literal falsity 1=`wel 0 0`. This positive
label statement requires typed inputs: an out-of-range bound index can
return label 0. The function-symbol branch is irrelevant on the actual
function-free set language. Invalid non-UFormula source inputs return 0.

The constructor equations retain equality symbol 0, membership symbol 1,
numeric Top 0 and Bottom 1, and the literal implication/relative-negation
encodings of conjunction, disjunction and existence. The underlying numeric
constructor still has the zero implication alias `wim 0 0=0`. This is a
syntax graph checkpoint; no theorem identifies `decode(encode(p))` with p,
derives its output in CProv, or translates internal source proofs.

The successful run2 checked the source in 10.078947 seconds and the focused
audit in 3.495564 seconds: 18 named axiom probes, 24 generic callers, and only
`propext`, `Classical.choice`, `Quot.sound`. The source had zero warnings.
The audit had one unused-simp warning for `if_pos rfl`; successful bytes
are retained without cleanup. Run1 failed on two singleton-versus-constant
parameter-vector equalities. The only proof repair adds
`Matrix.constant_eq_singleton` to the two wrapper normalization lists.

The narrow runner reuses exactly 13 project objects and four directly
encountered external source/object boundaries. Checked CProv evidence supplies
the numeric ancestors; checked 827 refresh evidence supplies Instances and
matching boundaries. Neither parent's fresh module is imported. The selected
Cantor object is the exact `fc2255ba…` object from the CProv parent, with no
new variant. Actual Init/Omega providers and all 46 immutable proof inputs
are hashed before and after. The complete Foundation namespace mirror is
available to Lean but is not independently or transitively attested.

The portable runner defaults to maintained source/audit/parent records and
accepts explicit repository, dependency, object-cache, namespace-cache and
library paths. Its relocation adjustment preserves the exact helper hash
recorded in each parent without requiring the parent's historical checkout
path. Prepare-only performs no compiler or version call and builds nothing.
The successful proof used 4 GiB, one thread, default Lean options, and a
120-second limit per command. No dependency was built or downloaded.

```sh
python Logic/Interpretability/ZFCinPA/check_validator_formula_encoder254.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --output /external/fresh/encoder-check
```

The existing CProv predicate supplies the original twelve rule closures.
The remaining reverse direction needs all-internal formula/variable
transport, source sequent rule induction, and the actual encoded ZF axiom
clients. A bundle's c is both a formula code and a variable label; renaming
accepted proofs row by row is not assumed. Full PA induction may be used for
the later environment/alpha proof rather than forcing all proof-existence
statements into IΣ1. There is no reverse consistency or binary endpoint here.
