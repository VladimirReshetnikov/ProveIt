# Uncompiled sign33 proof draft

`Sign33Draft.lean` drafts a direct call to the existing model-theoretic
`ArithmeticPellFirstIndex.scalar_window` and `maintained_first_indices` under
their full positive-input, fixed-port-bound, transport and four norm
hypotheses. It extracts `q-F-alpha>0`, `R+2<E` and `2*R<c`; the latter call
uses the original source index `i`, since the maintained theorem itself puts
`I = delta a * i * c * c` in its auxiliary equation, where `a` is the Pell
base. A separate model lemma
proposes deriving `f≥2` from the positive source index and the original strong
norm.

Three independent ordered-ring lemmas then derive the five desired signs
from the corresponding intermediate inequalities and the auxiliary equation:
positive gap and tau; positive `c*T−R` and `V`; and nonpositive `V²−y²`.
The statements do not assume the desired five signs. The intermediate bounds
are explicit, and the first-index theorem is an existing cited result, not a
newly checked result in this draft.

**No Lean file in this packet has been compiled.** Source presence checking
is not syntax or kernel validation; tactics, typeclass inference, definitions
and imports may need repair. In particular the ordered-ring lemmas have not
yet been connected to the natural-model windows, to the model difference-ring
embedding, or to the literal five seed norms. That connection must prove all
natural-versus-ring subtraction identities (using the scalar window), the
auxiliary `absdiff` square identity, the positive fixed-port casts and their
numeric bounds, and positivity of all shifted source coordinates. Nor does
this packet construct the nonnegative model-natural differences or prove the
sign33 zero bridge, degree/normalization, Jones instantiation, or iPRA result.

An alternative to the maintained theorem is the ordinary-first-index route
with `i` replaced by `delta a * i_source`; that path carries the same
source-to-model obligations. Run `python3 -I -S -B check.py` only for the
limited source-presence report. No Lean process was run.
