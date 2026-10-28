# Actual internal C222 membership-container witnesses

Authored and completely self-reviewed by `controller_certificate`, 2026-10-26. This packet adds only `ZFCinPA.ValidatorSeedWitness222` (123 lines) and its 50-line checks. It imports the frozen `ValidatorEind222` endpoint and produces actual new-checker proof witnesses over every internal arithmetic model satisfying IΣ₁. It does not invoke external Nat C222 completeness or assume semantic validity of a seed schema.

Frozen source SHA256s:

- Main: `fb0b8fc33cc081550caffb46ea819d03b6218034d8afa845bf990affc19eb010`.
- Checks: `60bbfbbd6b5fcdd86d5e97b7bbe21b999ec7158dd2d973ce4b4ad7ee0ac34f34`.
- Detailed replay JSON, `validator-seed-witness222-replay.json`: `c2d246c1ed29631779d4d3c67cb807d3a9aee73922346c8dc60c3e97ac203fcc`.

The connective abbreviations preserve false code 1. `not_all_imp_ex_conj` constructs both directions between the literal `¬∀i(p→¬q)` and the encoded `∃i(p∧q)`. These codes are not definitionally equal: the latter adds two negations around the universal's body. The proof uses the actual double-negation introduction/elimination certificates, universal monotonicity, and contraposition. This conversion is used twice: first to normalize the seed's `nks` component, then to normalize the inner request.

`seed_pair a b c` obtains `∃c(clos(a,b,c,c)∧req(b,c,c))` from the actual helper-free bundle under precisely `c≠a` and `c≠b`; `seed_request` projects the request. No positivity or unequal-input requirement is introduced. Checks explicitly retain the legal case `a=b=1,c=0` and expose its numeric history witness.

`request_eind_member b p k` proves `req(b,k,Eind(b,p))→p∈k` under exactly `b≠p` and `b≠k`. It uses the fixed membership substitution theorem to send `Eind(b,p)∧b∈k` to `p∈k`. Existential monotonicity and membership vacuity eliminate the request's output binder. Universal monotonicity then converts the request into `∀b(Eind(b,p)→p∈k)`; `Eind_ex` supplies the existential antecedent, and the same vacuity certificate eliminates the final existential. There is no assumed self-label matrix vacuity, primitive-equality vacuity, or existential-idempotence rule.

The literal arithmetic constructor bounds give `a<Eind(a,b)` and `b<Eind(a,b)`. Set `k=containerLabel(p)=Eind(p+1,p)`. The diagonal seed roles `a=b=p+1` are therefore legal, and the final theorem is

```text
CProv222(∃k (p∈k)).
```

Here `k` is the fixed numeric label computed before forming the formula; its displayed bound ensures it differs from the free member label `p`. GEN provides the corresponding universal closure at `p`. `membership_container_witness` unfolds the conclusion to `∃code, ArithmeticHistory222.value code = formula+1`. Checks include both arbitrary-model `p=0` and the actual Nat history witness at `p=0`. This is membership containment only. It is strictly weaker than `NativeTheory.containerAx`, which also requires transitivity and internal bounds for subsets; no CP/GIC result is claimed.

Both complete sources and the newly adapted private drivers were read before execution, and the complete final sources were reread afterward. The first main build failed while elaborating an incorrectly ordered application of `Eind_el_l`, exhausting default heartbeats. The independent read-only plan challenge by `complemented47_review` identified the exact argument order `p,k,b`. Correcting only this application made the pair pass without changing statements or raising limits. The rejected snapshot, diagnostics and timing remain pinned in the replay JSON; no failed object is accepted.

The final fresh main passed with empty diagnostics in 3.16 seconds; checks passed in 1.87 seconds. All eleven printed axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Maximum RSS was 1,818,708 KiB. Fresh object SHA256s are `c361601d3d32fd8b3a98903aaea35904b8b5b80f43a6ff635c0b45d6596787d7` and `6fce191383b7c129d5717254dbce6a68892b71e6064d018049cdb222690abda6`.

The private overlay is `/tmp/seed-witness222-controller-7tovl35a/lib`; its input-inventory SHA256 is `54e1f5b4d7edc6872421aeecf0345eaea52691a2b30de198b5ec1f43decd7637`. It authenticates 126 cached current-source modules, including 95 Foundation modules, 411 recorded object companions, and 38 explicit external import boundaries. Only the two new leaves were compiled, with Lean 4.32.0, `-M6000 -j1 -DElab.async=false`, private symlinks and a 512 MiB disk reserve. All selected source/object/compiler/manifest/external pins were checked before and after execution. No frozen source, shared object, or Git state was changed. This receipt records author validation and the limited peer plan challenge, not an independent replay of the final packet.

The larger internal calibration remains open. The existing R2 endpoint concludes CProv254, whose stronger bundle directly supplies container/GIC components. Reusing that conclusion for C222 would require new actual proofs of the stronger native axioms and an equality-interpreting all-formula/proof translation. The external `KSeedDirect222.seed_direct` semantic argument and its model-completeness use are not such an internal translation. This packet proves neither runtime calibration nor PA/HA provability of the final equation/consistency equivalence.
