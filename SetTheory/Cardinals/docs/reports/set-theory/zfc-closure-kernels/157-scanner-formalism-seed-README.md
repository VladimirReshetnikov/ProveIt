# A safe seed for the unchanged abstract source

The rejected shortened-scanner table has a finite startup trace reaching a
tape representing the source root at logical registers
`[4,3,0,0,3,0,0,0,0]`. Its later source simulation fails; this packet does
not certify that binary table. Native code `3 = E(0,0)` is derivable in the
unchanged C222 calculus. The complete proof is in `seed_calibration.tex`.
The current formula and cache are theorems, the zero stack is Good, and
the candidate cutoff and additive parameter may be arbitrary.

Soundness follows from the inherited invariant with this different base
case. Completeness uses the inherited strong proof-block compiler and
the cofinal family `AX(0,1,1,u)` followed by a fixed compiled refutation:
its candidate number is `P(3,P(1,P(1,P(u,r)))) >= u`, so omitting finitely
many initial candidates cannot omit every refutation program.

`seed_reflexivity_proof.json` contains 79 closed nodes deriving `E(0,0)`.
The independent `check_seed_reflexivity.py` verifies literal schema
instances, MP and closed GEN, without importing the builder. K and S are
explicitly inherited derived schemata of the unrestricted rho8 calculus.
This is ordinary mathematical evidence, not a newly compiled exact-machine
Lean or Rocq endpoint.

Run:

```sh
python3 check_seed_reflexivity.py
```

The optional `build_seed_reflexivity.py` deterministically reconstructs the
certificate using the unchanged upstream `hilbert.py`. The basis proof is
also the exact argument already formalized as `G222.refl222` upstream.

## Provenance

Repository snapshot: `704b87442afbd571833a628cd558f1d207fd8b2f`.

Read and used:

- `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq224/src/G222.v`:
  `refl222`, `ex_mono`, and the exact merged equality row.
- `.../L1_Sound222.v`: generic `Inv_step`, `Inv_run`, and `halt_step`.
- `.../L1_Comp222.v`: universal `blk`, `compile`, `program_halts`, drain,
  and command encoding; the cofinal START family is made explicit here.
- `.../Enum222.v`: exact scheduler, fields, stack and AX semantics.
- `Computability/BusyBeaver/Research/ZFC/k218-ks-mixed-commutation/hilbert.py`:
  copied unchanged as `hilbert.py`; its `eq_refl` builds the specialized
  finite certificate. Original authorship is retained in the source and
  the enclosing repository's attribution.

The new certificate extraction, independent checker, and seed proof are
the contributions of this packet. A future physical table must separately
establish both startup and unbounded binary simulation before this seed
theorem can be used to certify it. The shortened-scanner table fails the
simulation obligation and is not a valid 217-state construction.
