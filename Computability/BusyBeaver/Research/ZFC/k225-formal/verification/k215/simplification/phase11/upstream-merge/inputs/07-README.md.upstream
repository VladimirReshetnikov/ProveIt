# Rocq proposal: the rho8cd derivations for coq/215

Proposal only. The maintained Rocq tree is the peer's checked checkpoint; these files are offered for its
next check and are not wired into `regenerate215.py`.

| File | Replaces | Derivation | Bytes (before → after) |
|---|---|---|---:|
| [`CD222.v`](CD222.v) | `coq/215/CD222.v` (107 ported CD254 certificates) | [`../derivation_luk.txt`](../derivation_luk.txt), 56 lemmas | 22,865 → 12,007 |
| [`DomRho8.v`](DomRho8.v) | `coq/215/DomRho8.v` (reflective Source 149 replay) | [`../derivation.txt`](../derivation.txt), 52 lemmas | 22,673 → 11,190 |

Both are byte-for-byte outputs of
`python ../generate_domrho8_cd.py --derivation ../derivation_luk.txt --rocq-cd CD222.v` and
`python ../generate_domrho8_cd.py --rocq DomRho8.v`, and keep the public names their users need
(`thm_K`, `thm_P`, `thm_B`, `thm_S`; `DomImp`, `rho8_all`).

Checked here (Rocq 9.1.0 / rocq-stdlib 9.0.0, K230 reference at its pinned sources, in the
`.build/215` tree of the full 2026-10-21 closure build):

* `CD222.v` 5.5 s, then its users `Prop222`, `G222`, `Interp222` and `Complete222` (25.6 s), all
  closed under the global context;
* `DomRho8.v` 1.9 s and its user `ThmDom` 1.0 s, both closed under the global context.

Not run: a fresh compile of the whole closure and recursive `coqchk` with these files in place.
The Lean twins are maintained: `Lukasiewicz.lean` and `DominatedImplication.lean` are rendered by
the same producer.
