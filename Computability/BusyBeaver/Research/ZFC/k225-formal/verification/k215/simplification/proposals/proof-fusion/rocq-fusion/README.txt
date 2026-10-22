DIRECT COMPILATION INTO BLOCK CONTRACTS: ROCQ COMPONENT
=====================================================

Baseline: ProveIt 6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95.
This component changes no numerical constructor, command, machine row, source
program, implication derivation, or final seed theorem statement.

MATHEMATICAL CHANGE
-------------------
Let Compilable X mean `exists L, blk X L`, using the existing exact block
contract from L1_CompPerm. The maintained block proofs already establish:

  truth          blk_true
  modus ponens   blk_mp
  guarded rho8   blk_r8, provided u <= a

These operations form a DomImp instance for Compilable. Apply the existing
rho8_all theorem to that instance, obtaining a block for every unrestricted
rho8 instance. Now induct directly on thm222. The existing route first
translated thm222 to the intermediate inductive calculus thmDom, then
inductively compiled thmDom. The new route folds the derivation directly into
the algebra of programs satisfying the contract.

The existential witness occurs before the universal input quantifiers in blk:
one fixed finite command list works for every current formula and stack.
Early halting remains an allowed outcome of the block contract. Neither a
uniform bound on program size nor a minimal proof length is claimed.

FILES AND PRODUCERS
-------------------
compiler-fusion.patch updates the two rocqperm templates, their exact K215F
generated copies, and the two affected proof hashes in the extension manifest.
No unrelated hash or generation option changes. make_fusion.py reconstructs
the patch/overlay from the pinned checkout. The production generator's existing
namespace substitution and source-header hashing reproduce the changed files.
ThmDom is still generated and retained for existing separate calculus clients,
but it is no longer imported by either production compiler/seed module.

The old L1_CompPerm.compile identifier is intentionally replaced by
L1_CompPerm.compile_direct, whose premise is thm222 rather than thmDom.
The optional compat/CompilerDomCompat.v restores the old statement under
CompilerDomCompat.compile. This is explicit internal API migration; the four
existing enum/seed endpoint theorem types are unchanged and checked by Client.v.
Keeping the old theorem in its original module would keep ThmDom in its import
closure, defeating this dependency simplification.

MEASURED SOURCE EFFECT
----------------------
The existing generated compiler changes from 351 lines / 15,406 bytes to
362 lines / 15,782 bytes; the seed remains 59 lines, shrinking by 21 bytes.
ThmDom's 70 lines / 1,920 bytes leave the endpoint's selected source closure.
Net selected source saving: 59 lines / 1,565 bytes and one module.
The optional compatibility file adds 8 lines / 431 bytes outside that closure.
Counting the two maintained templates and generated copies together, the changed
production text grows by 710 bytes; there is no whole-repository size reduction.
The predicted maintained K215 closure is 236 rather than 237 modules. That is a
source-dependency result, not evidence of a rebuilt full endpoint.

VERIFICATION
------------
check1/verification.json and check1/logs retain the actual focused run:
Coq 8.18.0 / OCaml 4.14.1; 11 project/calculus modules plus a typed Client;
six closed Client assumption reports; successful recursive coqchk of SeedPerm,
CompilerDomCompat and Client, with no -admit or -norec option.
The maintained 1,169-line DomRho8 module is unchanged, so this run isolates the
compiler fusion from previous implication-shortening proposals.
Private Coq 8.x compilation copies replace `From Stdlib Require` with
`From Coq Require`; the receipt binds both original and compiled source hashes.

This component does not rebuild the physical-machine-to-ZFC endpoint and is
not a production Rocq 9.1.0 / rocq-stdlib 9.0.0 acceptance run.

REPRODUCE
---------
The exact production-format focused inputs are bundled in inputs/. With a
complete existing Coq or Rocq installation, run from this component directory:

  python3 check_fusion.py --out /tmp/rocq-fusion-fresh \
    --coqc /path/to/coqc --coqchk /path/to/coqchk

An optional --coq-root PREFIX configures an extracted Debian/Ubuntu toolchain
containing PREFIX/usr/lib/ocaml. An optional --repo CHECKOUT uses the current
checkout plus the provided overlay. Always choose a new output directory.
The checker obtains the existing shared proof-build lock for each compiler
invocation. Compiled objects are disposable and are not release deliverables.

INTEGRATION GATES
-----------------
Review the patch, run git apply --check against the pinned repository, regenerate
the production sources, and rebuild the affected descendants and exact sparse
and dense endpoint clients using the designated Rocq 9.1 toolchain. Refresh
source/object bindings and print the four endpoint assumption reports. Keep
the current full-endpoint evidence as evidence for its original source bytes.
After that production acceptance, one can independently adopt the already
proposed shorter implication core and normalized source certificate.

ATTRIBUTION
-----------
The command semantics, contracts and inherited mathematical lemmas are ProveIt
and its credited K230/Jeff ancestry. This component contributes the direct
contract-algebra instantiation and its integration; it does not claim the
underlying dominated-implication proof as new.
