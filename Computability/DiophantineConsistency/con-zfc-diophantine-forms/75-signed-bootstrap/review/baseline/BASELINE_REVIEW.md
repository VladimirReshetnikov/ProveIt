# Wave 10 independent baseline audit

## Scope and receipts

Eight original wave-9 archives, pinned in ../../INCOMING_PINS.json, were reviewed and replayed from fresh temporary copies. All eight root replays passed and every original source tree remained unchanged. Only verification timing receipts changed in two copies. All Python files were parsed and root execution surfaces inspected; no network/install/system-shell patterns were found. EXECUTION_SURFACE.json records imports, local process calls and source hashes. REPLAY_RESULTS.json and per-archive stdout/stderr give replay receipts. These are finite arithmetic/data audits, not universal proofs or newly kernel-checked consistency equivalences.

Independent topology, variable, and live-gate counts passed for 44 selected literal circuits. FRONTIER_COUNTS.json records their hashes and counts. Degrees are read from released exact-degree certificates covered by the root replay, not independently reproved by the count script. SELECTED_PARETO.json is only a Pareto comparison of selected circuits; historical lower-cost/high-degree points remain relevant and no global optimum is claimed.

## Current actionable frontier

- Unrestricted integers: quartic 41 (Structural Reductions), sextic 35 and octic 30 (Sign and Norm).
- Thirteen positive: degree 34 / 93 operations (Congruence Carriers), versus degree 114 / 83 (Sign and Norm).
- Twelve positive: degree 118 / 104 operations or SOS degree 172 / 103 (Congruence Carriers).
- Fourteen positive: degree 26 / 92 (Shared Taps), degree 30 / 83 (Structural Reductions).
- Fifteen positive: degree 24 / 88, 26 / 87, 30 / 78 (Gap Congruence). Historical low-cost/high-degree points are not superseded by these.
- Nine positive selected degree/operation frontier: 1494006/487, 1503378/483, 1510770/481, 1520178/476, 1663788/475, 1675396/458, 1738228/457, 1825540/451, 1834516/449, 1845940/444.
- Ten unrestricted: 3327556/519, 3507876/494, 3547076/490. These depend on the Sun reduction.
- Thirteen unrestricted without that reduction: 10461744/519.

## Contributions and overlaps

1. Gap Congruence combines gap coordinates, degree-separated coefficient packing, carry deletion, and a congruence-separated root norm. It also gives a direct local one-stack polynomial, but explicitly does NOT instantiate the global trace compiler into a completed small Con(ZFC) endpoint. Its 444-operation nine-positive form and 490-operation ten-integer form must be included in cost comparisons.
2. Positive Gap uses k=eta+zeta, p=P-k>0 and t=tau-p>0 to replace two Pell-related rows by p-Ec+eta E=0 and t^2+2pt-eta p-zeta p-1=0; q^2 replaces q^2-1 as a positive coordinate. It gives 1797796/465 and a 24/89 fifteen-positive companion, both currently dominated in these two metrics.
3. Oriented Guards proves a shared sign guard using the cofinal square scale w=4u^2, and supplies 42/36/32 unrestricted low-degree endpoints. Its refined nine-positive family still contributes the lowest degree1494006 and intermediate1663788. Its thirty-degree14-positive version is now cost-dominated by Structural Reductions.
4. Congruence Carriers successively restores q^3|Y then q|X by using stronger congruence carriers; a divided auxiliary norm and unit-product finalizer eliminate auxiliary coordinates. The 13-positive34 and12-positive118 endpoints are new strong degree records within this selected baseline.
5. Sign and Norm centers a Pell root before taking its norm, reducing the13-positive endpoint to114/83. Its cofinal scale/shared sign mechanism overlaps Oriented Guards and Sign Recovery. Moving the square guard from q to X before elimination enables35/30 unrestricted sextic/octic endpoints.
6. Sign Recovery independently uses the shared-sign cofinal square mechanism and an exact majorant-defect expansion. Its headline42 quartic is not the unique or smallest quartic in this intake; its nine-positive and14-positive pairs are dominated.
7. Structural Reductions uses U=Y^2 after q^3|Y and gcd(Y^2,H)|9, then delays the radix-sign recovery. X=2u^2 and q congruent1 mod2^d-1 recover the sign after packing. It reaches41 quartic and14-positive30/83.
8. Shared Taps reuses fixed-coefficient kernel positions and shares powers, contributing1675396/458 and1738228/457. Its successive carriers give14-positive26/92. Its ten-integer companion is dominated by other intake endpoints.

These overlaps rule out presenting the square-scale/shared-sign or direct-local-stack idea as newly unexplored in this iteration.

## Formal status at 9cca523d9f27ad39d52993f4065cbd7e58f8bdd4

The new formalization commit9a58fcecce75f9b41f65a409bd2848ae08809549 materially advances the source side. STATUS.md identifies SplitNineSource59.exists_natural_zero_iff_source_compact54 as checked: the authoritative old-z source, all89 kernel records, four explicit port boxes, no supplied height/degree/packing/population premise. Signed minus-form Pell step-down is also checked, but recovered main sequence, bootstrap and half-modulus hypotheses remain to be supplied by the actual source.

Do not conflate that achievement with authentic native consistency calibration. NATIVE_CALIBRATION52.md still explicitly requires the positive-zero equivalence for the coherent four-port native instance and BlankHalts machine215, including Pell/bit-mask, literal packed decoder, cell synchronization and finite tableau extraction/construction. The existing closed NativeZFC expression uses a DIFFERENT proof-enumerator graph and Jones compiler. Its closed theorem does not identify these native fixed ports.

Likewise object-language ZFC closure is separate: OBJECT_ZFC.md retains the internal proof-certificate and arithmetic compiler interpretation obligations, including nonstandard natural numbers of arbitrary ZFC models. Ordinary mathematical proofs formalizable in ZFC are not newly supplied object-language derivation files.

This audit reads pinned formal sources and status; it does not rebuild Lean or Rocq. FORMAL_SOURCE_PINS.json authenticates selected new sources to their Git blob hashes. Do not describe the fresh replay as a proof-assistant build.
