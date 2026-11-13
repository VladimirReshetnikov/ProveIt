# Natural 80 own-zero units and conditional main norm

`Natural80OwnZeroNorm.lean` is an **unelaborated source-only proposal**
using the separate [80 J-positivity](../ordinary14-natural80-jpos-model-draft/)
and [80-to-74 partial-valuation](../ordinary14-natural80-partial74-bridge-draft/)
drafts. It has not been run in Lean, and its imported drafts, rewriting and
tactic behavior may require repair. The source checker pins and inspects
the relevant interfaces; it does not establish a model theorem, axiom
audit, iPRA result, or physical coefficient/PDF binding.

`units_of_80_zero` proposes extracting the 74 first Pell equation and four
factor-unit equations from an 80 own zero. Its premises explicitly require
representations `(p 0 : DiffRing V)=ι beta` and `(p 1 : DiffRing V)=ι K`,
plus `beta>0` and `K>0`. It uses the proposed J-positivity result, the
partially shifted 74 valuation, the three literal mod-four exclusions, and
`OwnZeroProduct74Draft.factor_units_of_zero`. Only the resulting 74 slots J,
w, and s need be positive; f, r, y, and gamma are not assumed positive.
The statement accepts arbitrary integer ports MC and MF at this stage and
does not assert rank-window inequalities.

`main_norm_of_unit` proposes converting an explicit 74 main-factor unit to
the signed-magnitude square norm via the existing fact-level
`ArithmeticAdaptiveScaledNorms2011.unit_square_norm` and
`ArithmeticAdaptiveTransport2011.magnitude_equivalent`. It **explicitly
assumes** both the literal `Dstar` signed-pair representation `(P,N)` and
the natural pair `(rhs,0)` for the main right-hand expression. Neither
binding is proved here, and this conditional lemma is not yet an
application of `DirectMainNorm.direct_main_orientation` to an 80 zero.

To complete the model path, prove those literal pair bindings with all
needed port casts and inequalities: in particular, the root representation
requires the actual MC and MF symbolic ports to be represented by model
naturals, and the natural definitions involving `q−F` and `q²−1` require
their corresponding bounds. Derive the guard gap `F+alpha<q` without using
an all-positive-gamma lemma; supply positive beta and the explicit MC/MF
rank-window bounds. Then connect the obtained main norm, first Pell
equation, index bounds, and rank inequalities to the separate
[narrow gamma contradiction](../ordinary14-natural80-gamma-narrow-draft/).
The two `#print axioms` commands have not been executed.

An [independent source review](../../reviews/ordinary14-natural80-ownzero-norm-independent/README.md)
checks the partial valuation and explicit assumptions, including the two
still-conditional main-factor pair bindings.

```
python3 -I -S -B research/ordinary14-natural80-ownzero-norm-draft/check_source.py > /tmp/natural80-ownzero-norm.json
cmp /tmp/natural80-ownzero-norm.json research/ordinary14-natural80-ownzero-norm-draft/result.json
```
