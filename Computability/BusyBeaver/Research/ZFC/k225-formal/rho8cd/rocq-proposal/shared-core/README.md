# Rocq proposal: one shared implication core for DomRho8 and CD222

Proposal for the peer's Rocq checkpoint; nothing here is wired into `regenerate215.py`. It is
the Rocq counterpart of the Lean shared-basis proposal (`3a7a61ee97`, `49e99c5b7c`): one
condensed-detachment derivation serves both the dominated calculus and the unrestricted one.

| File | Role | Lines / bytes |
|---|---|---:|
| [`DominatedCore.v`](DominatedCore.v) | generic `Section`: any `imp`, any reflexive `below` closed under insertion into either operand, modus ponens and the restricted rows derive `rho8_all`, `composition`, `lift_right`, `k`, `peirce`, `s` | 268 / 12,943 |
| [`DomRho8.v`](DomRho8.v) | replaces `coq/215/DomRho8.v` (reflective Source 149 replay): the core at natural codes with `<=`; same `DomImp` record and `rho8_all` statement | 23 / 1,009 |
| [`CD222.v`](CD222.v) | replaces `coq/215/CD222.v` (107 ported CD254 certificates): the core with `below := True` over `thm222`; same `thm_K`, `thm_P`, `thm_B`, `thm_S` | 31 / 1,408 |

The two maintained files total 1,399 lines / 45,538 bytes; the three proposed files 322 lines /
15,360 bytes.

`DominatedCore.v` is rendered from [`derivation_shared.txt`](derivation_shared.txt) (the 58-step,
six-goal derivation of `3a7a61ee97`) by the renderer of `49e99c5b7c` with
[`rocq-core.patch`](rocq-core.patch) applied:

```sh
git show 49e99c5b7c:Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/generate_domrho8_cd.py > gen.py
patch gen.py rocq-core.patch
python gen.py --derivation derivation_shared.txt --rocq-core DominatedCore.v
```

The adapters `Require` the core without `Import`, since its generic `rho8` would otherwise shadow
`Codes230.rho8`.

Checked (Rocq 9.1.0 / rocq-stdlib 9.0.0, K230 reference at its pinned sources, one `coqc` at a
time in the `.build/215` tree): `DominatedCore` 1.3 s, `DomRho8` 0.8 s, `CD222` 0.7 s, each closed
under the global context; then the maintained users `Prop222`, `G222`, `Interp222`, `Complete222`
(31 s) and `ThmDom` against them. Not run: the full closure compile and recursive `coqchk`.

Adoption needs `DominatedCore.v` added to `coq/215` and to the compile order before `CD222` and
`DomRho8` (it has no project dependencies), and the regeneration and manifest records refreshed.
