Guarded source jump-to-decrement equivalence

Run: python3 verify_zero_jumps.py

The standard-library verifier reads the pinned Program.lean, reconstructs
all 3812 ordinal source instructions and control successors, computes and
checks the finite joint zero-pattern invariant, and verifies the exact
restricted transition identity after source26 CB1 -> CD6 and after all10
eligible CB1 -> CD6 substitutions together.

Files:
  zero_jump_equivalence.tex: self-contained mathematical proof and precise
    separation from physical instruction binding and blank initialization.
  joint_mask_certificate.json: 3812 hexadecimal bitsets; bit m of entry i
    means the nine-register positivity mask m belongs to the invariant at i.
  zero_registers_by_site.json: registers known zero at each source site.
  source26_cd6.json, all_eligible_cd6.json: complete source instructions.
  receipt.json: exact finite census, hashes, and eligible replacements.

The initial source configuration is pc25, R0=2, all other registers0.
It is represented abstractly by (25,1). The abstract positive decrement
has both positive and zero outcomes; this includes all natural values.
The closed invariant has274880 site-mask pairs, not274880 concrete steps.

No sub196 transition table, blank startup, new Lean kernel verification,
or implementation of an internal PA proof is claimed by this packet.
The note describes a PA-formalizable simulation proof at source level.

Program.lean is unchanged James Chang PA196 input; its source identity and
copyright attribution are retained by the encompassing research archive.
The verifier here independently reconstructs the graph and finite invariant
used by work/zero_jump_search.py, rather than accepting that script's data.
