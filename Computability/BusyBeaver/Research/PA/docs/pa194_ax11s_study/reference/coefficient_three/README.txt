INHERITED RESTRICTED-IMPLICATION PROOF DEPENDENCY

All copied source files are unmodified. Their pinned source paths, hashes,
Git blob identifiers, and URLs are in PROVENANCE.json.

reference/RestrictedImplication.lean is James Chang's generic finite
derivation of the K and S implicational schemas from the restricted
implication head and modus ponens. It has no imports; it states the
abstract rule and order hypotheses explicitly. Its MIT license is retained
as reference/LICENSE.JamesChang. UPSTREAM_README.md documents ProveIt's
upstream snapshot provenance (jamesyc/BusyBeaver commit
407cdc356f6b586635e71ac92be394255f4bfea4).

expand_basis.py and verify_primitive.py are the earlier ProveIt packet's
small generation and independent checking programs. They expand the
PREVIOUS small E(1,0)=I(0,1) obstruction into primitive restricted-head,
modus-ponens, generalization, and fifth-head steps. To regenerate and
verify that inherited certificate in a temporary copy of this directory:

    python3 expand_basis.py
    python3 verify_primitive.py

They create a larger primitive_proof.json and are not run by the new
cofinite checker. The historical generator's parser is not trusted by its
independent certificate verifier. previous_obstruction.tex explains that
earlier certificate. These programs and that report fragment retain the
ProveIt MIT No Attribution license in LICENSE.ProveIt.

The NEW all-cutoff argument is in ../../proof/cofinite_collision.tex.
Its ../../proof/check_cofinite_collision.py checks the fixed 21-line
derived-rule certificate, identifying K and S as the inherited derived
rules above. No new Lean/Rocq compilation is claimed. The new all-cutoff
theorem is proved algebraically in the report, not inferred from its
eight numerical test instances.
