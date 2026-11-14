# Attribution and contribution

This package is based on Vladimir Reshetnikov's ProveIt repository at
commit `317b07268681b44ff352d173a162e2a8c241b2fe`, particularly the PA194,
PA194Q, coefficient-family, and incoming NS research materials. It also
uses James Chang's imported PA196 source and the inherited independent
literal-tape engine. Retained licenses are in `licenses/` and the relevant
reference directories. Third-party material retains its original license.

New work in this package comprises the Q5/Q6 combinations, their builder
integration and exact certificates, independent binding and audit wrappers,
the complete current-corpus comparison, the report and proof integration,
additional allocation and invariant/marking searches, and packaging.
Premise exchange, the coefficient-five/six coding idea, and the underlying
interpreter and local-fold architecture are attributed prior work.

The documents in `calibration/` explicitly retain their mathematical
provenance. They are supplied to expose the logical dependencies, not to
represent inherited calibration as a newly kernel-checked development.

The unchanged construction compiler and symbolic runtime retain some
legacy functions for their earlier standalone entry points. The new
`construction/build.py` selects the bundled raw table and program before
using that code. Those dormant legacy entry points are not the supported
reproduction interface. The independent literal-tape verifier uses its
own bundled reference engine and reconstructs its list lemmas from the
candidate tables.
