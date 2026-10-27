# Proposed actual C222 stream selection leaf

Read-only proposal by `controller_certificate`, 26 October 2026. This narrows the earlier substitution/opening proposal to Streams222 alone. No new Lean source, compiler invocation or cache copy was made. Frozen Substitution222 remains unchanged and is not a prerequisite of this leaf.

## Scope and exact graph

Proposed files: `ZFCinPA/ValidatorEnvironmentStreams222.lean` and focused Checks, about 140–165 main lines and 45–60 checks. Sole import: accepted `ZFCinPA.ValidatorEnvironmentAlpha222`. Old Streams254 was fully reread as an arithmetic/source-structure guide; no old CProv254 or Alpha254 result is imported.

Define the fixed graph before ambient-model parameters, with argument order output, bound, seed:

```text
alternateStartDef : Sigma0.Semisentence 3 :=
  out bound seed. exists r<2, remDef r seed 2 and
    ((r=0 and out=2*(bound+2)+1) or
     (r!=0 and out=2*(bound+2))).

alternateStart bound seed :=
  if seed%2=0 then 2*(bound+2)+1 else 2*(bound+2).
```

Under an arbitrary internal IΣ1 model, prove the actual graph equivalence (`alternateStart_defined`, with optional explicit graph/unique-output wrappers). Its arithmetic needs only internal remainder mod2, nonnegativity and linear inequalities; it is not a search, external Nat parity computation or semantic truth oracle.

The finite-resource endpoints are:

```text
streamEnv_of_lt : B<s -> StreamEnv s B
streamFree_of_bounds : F<s -> 1<s -> StreamFree s F
apart_of_mod_ne : s%2 != t%2 -> Apart s t

bound < alternateStart bound seed
1 < alternateStart bound seed
seed%2 != alternateStart bound seed%2
Apart seed (alternateStart bound seed)

alternateStart_resources F B B' seed :
  let u := alternateStart (F+B+B') seed
  StreamFree u F and StreamEnv u B and StreamEnv u B' and Apart seed u.
```

`FreeAvoid z F` is the actual conjunction `z!=1` and avoidance of each stored label `F.[i]` for i<lenF. `nth_le` bounds every stored label by the vector's numeric code. Since all internal k are nonnegative, a stream beginning above that bound avoids all labels forever; a separate lower bound above1 handles fallback1. Reducing equality of stream elements modulo2 proves Apart. Repeated or zero stored labels are permitted; no positivity or distinctness premise is introduced. Arbitrary stream seeds, including0, are permitted for the selector.

The resource theorem supplies only the **new** stream's safety. It does not imply that the original seed already avoids F or either stack. Nor does it claim a single parity stream disjoint from both parity classes.

## Actual CProv composition and overlap

Using the accepted explicit IΣ2 alpha theorem, expose:

```text
encode_formula_relabel
  (hp : IsFormula set p) (hs : StreamFree s F) (ht : StreamFree t F) :
  CProv222 (encode222 F 0 s p -> encode222 F 0 t p) and
  CProv222 (encode222 F 0 t p -> encode222 F 0 s p).
```

When the seeds have different mod2 residues, `apart_of_mod_ne` allows `encode_formula_alpha` directly. When residues agree, set u=alternateStart F s. The graph/resource lemmas give StreamFree u F and Apart s u; equal residues give Apart t u. Two applications of actual Alpha yield s↔u and t↔u. Actual finite `compose` combines the forward s→u with reverse u→t, and forward t→u with reverse u→s. Both proof directions remain actual CProv222 certificates, not an equality of formula codes.

The required overlapping client is:

```text
encode_formula_next (hp : IsFormula set p) (hs : StreamFree s F) :
  CProv222 (encode222 F 0 s p -> encode222 F 0 (s+2) p) and
  CProv222 (encode222 F 0 (s+2) p -> encode222 F 0 s p).
```

Use `streamFree_next hs` and the preceding relabel theorem. Do not supply Apart s(s+2): the streams meet at indices1 and0. A focused negative check should explicitly refute that Apart premise. Also check equal seeds, seed0 selection, stored zero/repeated labels, and fallback1 avoidance.

All stream arithmetic and graph lemmas use IΣ1. Only the formula-relabelling/next clients require IΣ2 because they invoke accepted uniform Alpha; there is no new Π2 induction in this leaf. Source p must be a typed depth-zero formula. No claim is made for typed source0, unsafe original streams, nonempty contexts, arbitrary source substitution, quantifier inference under hypotheses, CP/GIC, full proof translation, or HA theoremhood. No new assumption that a formula is vacuous in itself or that an Eind auxiliary label is fresh is needed.

## Exact cache and frozen-source boundary

The existing plan entry `plans.streams` in `research/c222-substitution-opening-cache-plan-20261026.json` has SHA `16d3cbc7ac69f4386b9dd02cba242c98de51e79a6d0fc6cff4d029e7b9bb0c19`. A new read-only postcheck, `research/c222-streams222-cache-postcheck-20261026.json`, SHA `6fac5c63fb7c301ea095de37ec1f7aa93e6a1af61ac7a36ed8e47c105d7771d7`, reverified all selected imports and 706 source/artifact/compiler/manifest/root-record hashes.

The closure is exactly **156 cached sources / 117 Foundation modules / 507 prerequisite artifacts / 40 explicit external primary boundaries**, including Aesop and Init. Zero Foundation or other prerequisite refresh is proposed. Reuse accepted Alpha primary `/tmp/validator-environment-alpha222-root-peer-sduorx47/lib/ZFCinPA/ValidatorEnvironmentAlpha222.olean`, SHA `0e905fe0fb08c3052ecfa8c46ccfc4d881e7590b677b36b5eebd8777823280e1`, bound to root record `5f2bdbc02ef0c245670402c50c0c5035ad910fccb884c02f7aa7f353c301d50b`. Historical provenance distinctions in the parent inventory remain unchanged.

The authoritative substitution files are only the existing ZFCinPA-path main and Checks. A current `rg --files` and targeted read-only git status found no same-named DiophantineConsistency wrapper. My source and execution records never created or required such wrappers. Their frozen hashes remain `db2374e4...` and `9ee53adb...`.

If this leaf is approved, use only private symlinks/output paths and the accepted package boundary with `-M6000 -j1 -DElab.async=false`, rechecking the reserve before each run. Free disk at this read-only postcheck was 538,636,288 bytes, only about1.77MB above the 512MiB reserve. No compilation is authorized by this proposal itself; the current work stops after saving it.
