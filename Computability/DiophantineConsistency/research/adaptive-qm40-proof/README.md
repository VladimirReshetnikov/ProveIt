# Forty-variable quartic Lean proof inputs

The proposed proof rewrites the 41-variable quartic's second scaled root as
`mainScale * quotient`. `verify_literal.py` compares every row of the Lean
literal against the pinned 166-operation candidate graph. The context provides
30 common-residual substitution identities; the zero and map modules reduce
the comparison to those identities and the main norm. The norm module uses the
positive-scale quotient lemma. The model module proposes positive witness maps
in both directions in arbitrary IΣ₁ models, and the native module proposes the
fixed-port theorem by composing that model bridge with the 41-variable one.

The context, zero, maps and norm modules had exploratory compiled objects from
an earlier provider. The complete model and native modules have not yet been
compiled or subjected to a guarded replay. No new model or native endpoint is
claimed on the basis of these source files. The former package provider now has
broken links; a replacement requires independently documented provenance and
the resulting verification must retain its ancestry qualifications.
