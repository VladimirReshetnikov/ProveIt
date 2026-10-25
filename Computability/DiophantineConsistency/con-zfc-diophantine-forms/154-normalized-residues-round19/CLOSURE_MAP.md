# Ordinary proof and executable dependency closure

The release separates finite polynomial checks from the ordinary unbounded
mathematical arguments. It does not decide consistency or rebuild a new
end-to-end proof-assistant certificate.

## Direct signed family

`signed/` contains all current residual systems, actual expanded coefficients,
frozen integer transformation certificates, independent verification and the
full new proof. `signed/inherited_common/` is the unchanged direct component
of the authenticated incoming Common Remainders archive. It supplies the
252-variable arithmetic source, normalized-remainder theorem, source proof
texts, original arithmetic compiler and complete source reconstruction.
Its `upstream/round17/` subtree preserves the earlier signed orientation,
factorial, CRT, range-decoding, arithmetic and C222/ZF/ZFC calibration sources.

## Height-one family

`height_one/` supplies actual polynomials with all nonzero coefficients equal
to plus or minus one, incidence certificates, source equations and exact
reconstruction. Its source binding file identifies the exact signed equations.
The current exposed247 source is in `signed/exposed247/`. The two older sphere
sources are in `round18_closure/signed/sphere_grouped_centered_merged_odd/`
and `round18_closure/signed/sphere_sparse_centered_merged_odd/`.

`round18_closure/signed/` retains the original proof, six pinned source JSONs,
producer, independent checker, and the two complete selected endpoint sets.
Its eight inherited proof texts are copied unchanged under `inherited_proofs/`
for existing textual references. Identical originals also occur in the
common source closure above. This intentional small duplication preserves
readability; the old full report and ten unused sibling outputs are omitted.
`check_old_signed.py` verifies precisely the two retained outputs and rebuilds
their twelve artifact files byte for byte without referring to omitted data.

## Small-variable family

`scalar/` contains the new fixed-frame degree-minimum theorem and the
unchanged attaining eleven-variable degree-300, 148-operation equation.
Its six complete numerical ports, finite reconstruction recipe, baseline
proof and inherited source/license closure are retained. The independent
checker verifies 23 complete highest homogeneous forms against the literal
DAG. No new scalar numerical endpoint is claimed. Rejected exploratory
candidates are not included.

## Verification scope

`VERIFY_PLAN.json` is the authoritative command list. The top-level verifier
checks the exact inventory, copies the package to a disposable directory,
and runs that plan. Receipts must be written outside the sealed directory.
The source package needs neither a researcher workspace nor a network.
TeX rebuilding additionally requires an ordinary TeX Live installation.

Historical proof and interface files are preserved with their notices.
Their mentions of earlier research layouts describe their original context;
this map specifies the current portable closure. Full historical archives
are not reproduced and their top-level release checks are not advertised.
