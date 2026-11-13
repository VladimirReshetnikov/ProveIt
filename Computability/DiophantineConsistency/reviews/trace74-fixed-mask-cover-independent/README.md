# Independent audit: fixed payload mask coverage

**PASS for the external fixed-payload inequality.** Reviewed checker SHA-256 `c3eff677303bf8c8718fbb9b5c9edf8e4544bd279498a4ef1068ecf749dd1702`, observation SHA-256 `b57bffe2c997e0b9fe5cd94f20620ff0d9ea3cd9d8671f2d8b33b0509482f8dc`, and then-current README SHA-256 `792083fbe3eabf5794e6e3d8e5a1ed67bd969ce33f89a93d77a641448a82d014`. The observation records checker exit 0.

Independently read the candidate JSON SHA-256 `dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353`, decompressed the referenced parent payloads for beta, MC and MF, checked each compressed-parent and raw SHA-256 against its JSON record, and recomputed the integers. The values satisfy `beta=2^590069-1`, `0<MC<beta<MF<2*beta`, and `HP=MF-beta` has bit length 589954 while `beta-MC` has bit length 220833. Consequently `HP>=2^589953>beta-MC`, so `MC+HP>beta` and, for natural integers, `beta+1<=MC+HP`.

This is an external finite computation about those exact payloads, not a Lean equality to symbolic BFS ports or a proof that any saturation/no-carry condition follows from a 74 zero. The proposed scalar argument from explicit mask coverage and second no-carry is separate and remains subject to its own Lean check. No graph-zero, fixed-port guard or iPRA equivalence is asserted.
