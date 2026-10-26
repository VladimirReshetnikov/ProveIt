# Constructing the Boolean choice and all affine target subsets

Date: 2026-10-26. ROOT authored these compositions and read every final
source/check file before execution. This is an author self-review.

| Source under `Lean/DiophantineConsistency/` | Lines | SHA-256 |
| --- | ---: | --- |
| `ControllerAuxiliaryChoice.lean` | 50 | `e0ad958407b2888631f18c292a08c2de1af0b36297c9513e93d5f70ad4bcf251` |
| `ControllerAuxiliaryChoiceChecks.lean` | 37 | `c9e0a7f6deca29550488b79f51eff60895a949a87ad207741c619379ddfd162d` |
| `ControllerResidueLift.lean` | 68 | `5b421650fb7565cb3c38f5e4819fdba7b46f61d8d1e37bc3ed786ac6ca2268cb` |
| `ControllerResidueLiftChecks.lean` | 35 | `1fa74f933a4bc4c2859a58734e341e028855e6027f9fd4eaf4bc092038daa328` |

The actual `ZMod.castHom`, its natural-cast law, prime coprimality lemma,
and complete interval/orbit-transport sources were read. The generic
orbit module and its interval prerequisite were independently authored
and reviewed earlier. Existing prerequisite objects were reused.

For a prime p dividing nonzero C0, projection to ZMod p is an actual ring
homomorphism. The Boolean bit e is constructed as0 or1 so that t−e*b is
nonzero after this projection, assuming only that b's projection is
nonzero. Its least representative a satisfies `0<a<C0` and is coprime
to every p-power. No desired cardinality is supplied as a premise.

The quotient lift uses the exact canonical value of a residue z modulo
C0*T. Equality of its C0 projection to a proves `z.val%C0=a`. Its quotient
`z.val/C0` is below T by the actual representative bound, yielding u with
`z=a+C0*u.val`. Natural division and remainder are used before casting;
there is no unsupported inverse of C0 in the composite residue ring.
Zero residues and T=1 are retained by this helper.

Combining these constructions with `ControllerOrbitTransport` proves
that every target modulo C0*T is the sum of an actual finite subset's
affine weights and one Boolean multiple of b, when `T=p^n>C0`.
The constructed subset has exact cardinality `0<a<C0`. Its coordinate
injection and affine formula are explicit structural inputs, not a
supplied target-subset witness. No assertion identifies actual powers
of B with these coordinates. LTE, the actual orbit, safe dummy positions,
rank mutation and the equation converse remain open.

All four final builds ran under pinned Lean4.32.0, `-M6000 -j1` and
declared `Elab.async false`, writing their named module objects. Each
main was followed by its checks importing that fresh object. Every
terminal result was exit0, both main logs were empty, and all four axiom
reports use only `propext`, `Classical.choice`, `Quot.sound` or a subset.
No `sorry`, `admit`, `native_decide` or new axiom occurs. No full dependency
or umbrella replay is claimed.

Checks include characteristic2, zero/nonzero targets, failure of a zero
translate, actual prime projection, exponent0, explicit quotient13=3+5*2,
zero-residue/T=1 lifting, and all targets modulo54 using composite C0=6,
T=9 with no supplied subset. Both complete main/check pairs passed on
their first runs.

| Root log | SHA-256 |
| --- | --- |
| `/tmp/controller-auxiliary-choice-root-main.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/controller-auxiliary-choice-root-checks.log` | `a6869191237788daf40ba490d499dd5ba11061f5c295b3279cc9a6299326ae13` |
| `/tmp/controller-residue-lift-root-main.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/controller-residue-lift-root-checks.log` | `00d130703fdb29852b1a6444613e14ade9c2a178b1bcc3ef5980b4ebb2362dcb` |

The maintained equation, decimal numeral, fixed data and unknown names
are unchanged. Independent composition review is recorded separately.
