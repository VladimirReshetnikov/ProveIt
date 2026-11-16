# Site 27 positive branch: staged coherent rebuild

`check-site27-coherent.sh` extends a retained unified source-step build into a fresh directory by tracing the imports of `PA194Path27To28` and rebuilding every missing machine-specific source in dependency order. It audits that theorem's printed axioms and refuses `sorryAx` in every new source's output. The path-to-path theorem preserves arbitrary other registers and the complete numeric suffix under its single positive-branch hypothesis, with an exact clock.

The required unified baseline is pinned by the SHA-256 of `unified-coherent-manifest.json`. Its objects are copied into independently allocated files and byte-checked; an object receipt is recorded. Neither the input baseline nor any existing object is overwritten. The only fallback roots are the two general foundation roots and the ordinary Lake search paths; machine-specific fallback objects are rejected. Source hashes are recorded and checked again after compilation.

This is a staged rebuild, not independent verification of the retained unified baseline, its startup/header prerequisites, or the precompiled general foundations. The baseline's manifest pin and copied-object receipt alone do not establish the original object provenance. A complete audit requires the documented coherent prerequisite rebuilds and separately trusted general foundations. This all-model physical-run result does not prove either consistency implication or a full source simulation.

Call the wrapper with `REPO UNIFIED_BASELINE PROJECT_FOUNDATION PACKAGE_FOUNDATION NEW_OUTPUT`. Sources default to `Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code` beneath REPO; `PA194_SITE27_SOURCE_DIR` overrides that directory. The session baseline is `/dev/shm/pa194-unified-coherent/build`; project and package roots are `/tmp/current14-standard-fresh-build-20261104/lib` and `/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib` respectively. The output must not already exist, overlap the baseline, or contain symlinks.

The staged rebuild on 2026-11-14 passed all 54 additional source modules
and the named path-to-path axiom audit without `sorryAx`.
