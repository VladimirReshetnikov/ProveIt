# K215 calibration audit notes (source inspection)

Repository snapshot: `cdd582bec13f908df3711fa9e05d1ddac368a5db`, observed on 2026-10-22.

## Exact machine and mathematical interface

`Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` has 215 working states, 430 actions, blank input, initial state 0, and halt 215. Dense file SHA-256:

`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.

Native file SHA-256: `9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.

Source `sites215.json` SHA-256: `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`.

Lean module `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` states, without theorem parameters or consistency premises:

```lean
theorem blank_halts_iff_zfc_refutation :
  BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot
theorem nonhalting_iff_zfc_consistency :
  (¬ BlankHalts machine215) ↔ ¬ BProv ZFCax_s [] Form.fBot
```

The independently typed client at `k225-formal/verification/k215/independent-audit/EndpointAudit215.lean` expands blank halting as `∃ t : Nat, (KDense215.machine215.run t).state = none` and gives the same unconditional biconditional.

Rocq module `k225-formal/rocq/rocq-extension/coq/215/CorrectDense215.v` states:

```coq
Theorem tm215_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
Corollary tm215_nonhalting_iff_ZFC_consistent :
  (~ Dense.halts dense_tm Dense.c0) <-> ~(StandardZFC ⊢TC ⊥).
```

## What the existing records establish

The fresh full-build records were taken at `613f9cf28a`: Lean 4.32.0, 204 project modules and two endpoint clients; Rocq 9.1.0, 237 sources and recursive coqchk. Subsequent simplification records are incremental and should not be called a new full replay. The inspected raw Lean `lean/actual/audit/independent/compiler.log` lists only `propext`, `Classical.choice`, `Quot.sound` for both endpoint theorems. The inspected raw Rocq `rocq/actual/K215F.CorrectDense215.log` consists of two lines `Closed under the global context`.

This audit is source/log inspection, **not** a fresh execution of either kernel.

Repository README explicitly distinguishes external proof-assistant theorems from a separately encoded proof within ZFC (and does not claim a PA internalization). The ordinary mathematical calibration is stated to be formalizable in ZFC. A new article should distinguish that standard mathematical formalizability argument from supplying a checked internal ZFC derivation.

## Smaller source interface

The 430 TM rows need not be the Diophantine input. `KEndpoint.c222_iff_zf_refutation` states

```lean
KCode222.C222 Code254.F ↔ BProv ZFax_s [] Form.fBot
```

and `ConstructibleChoice.zf_refutation_iff_zfc_refutation` converts ZF to ZFC. The source endpoint `KEndpoint215.p215_boot_iff` and `L2Perm.dagPerm_seed_iff` connect the calibrated numerical calculus with the source program.

`Code254.lean` defines the following integer polynomials (over nonnegative arguments):

* `P(x,y) = ((x+y)(x+y+1))/2 + y` (Cantor pairing).
* `I(x,y)=4P(x,y)=2(x+y)(x+y+1)+4y`.
* `R(x,y)=I(x,y)+1`, `A(x,y)=I(x,y)+2`, `E(x,y)=I(x,y)+3`.
* `F=1`, `N(x)=I(x,1)`, `And(x,y)=N(I(x,N(y)))`, `Ex(x,y)=N(A(x,N(y)))`.

The C222 calculus is the least set of natural numbers closed under 12 rule families: truth 0; modus ponens from t and I(t,b) infer b; generalization from h infer A(a,h); rho1--rho6, merged equality G, rho8, and the seed bundle with side conditions c≠a,b. The complete constructor definitions are in `KCode222.lean` and `Code254.lean`.

The kernel proof is not circular. `KUpper222.zf_refutation_of_c222` uses constructible-universe reflection to show the seed bundles hold in a model obtained from a ZF model, plus soundness/completeness. `KEndpoint.c222_of_zf_refutation` uses completeness for the numerical calculus and constructs a well-founded part of a quotient model from the seed model, contradicting a supplied ZF refutation. `ConstructibleChoice` transports model existence via Gödel's constructible universe. No consistency statement is added as an axiom.

## Stable source links

Base: `https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/`

* `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean`
* `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/CorrectDense215.v`

## Meaning of the syntactic consistency predicate

`Logic/FirstOrder/Lean/FirstOrder/Completeness.lean` defines

```lean
def BProv (B : Form → Prop) (G : List Form) (phi : Form) : Prop :=
  ∃ Gb, (∀ x ∈ Gb, B x) ∧ Prov (Gb ++ G) phi
```

`Prov` in `Logic/FirstOrder/Lean/FirstOrder/Calculus.lean` is finitary classical natural deduction with equality: assumption, introduction/elimination rules for the connectives and quantifiers, excluded middle, equality reflexivity, and the Leibniz rule. The initial `B` in BProv is background theory, not a numerical proof-length bound. The endpoint is ordinary unbounded syntactic consistency despite the namespace `BoundedZFCConsistency` used for the choice definitions.

`SetTheory/ZF/Lean/ZF/Zf.lean` defines `ZFax_s` by universally closing Extensionality, Pairing, Union, Powerset, Infinity, Regularity, all Separation schema instances, and all Replacement schema instances. `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Choice.lean` defines `ZFCax_s` as this theory plus the sealed Zermelo selector formulation of Choice (every pairwise disjoint family of nonempty sets has a set selecting exactly one point from each). The file explicitly states that equivalence to the choice-function formulation over ZF is standard object-theoretic mathematics and is not formalized in that particular module. One may either define Con(ZFC) using precisely this standard effective axiom presentation, or invoke the usual explicit finite proof translations between standard presentations.

The `candidate-k215/proof.md` exposition explicitly concludes, by ordinary reasoning formalizable in ZFC, that `Halt(K215,blank) ↔ ¬Con(ZFC)` and its negation. The elementary machine simulation and the numerical-calculus calibration use set-theoretic constructions available in ZFC: finitary syntax, first-order soundness/completeness, constructible models, and a well-founded quotient model. The existence of an external Lean/Rocq theorem alone should not be presented as a mechanically checked translation of that proof into ZFC syntax. The mathematical formalizability statement and the external formal verification are distinct evidence layers.

## Binding the new finite compiler to the exact source

The new `verify_k215.py` parser rejects any dense-table byte sequence whose SHA-256 differs from the pinned value above. It checks all 430 state/read keys, the exact start declaration, state and symbol ranges, and transition uniqueness. It parses the literal tables in Lean `KDense215.rows215` and Rocq `Table215.table215` independently, then compares every transition with the dense table. The observed source identities are:

| Source | SHA-256 |
| --- | --- |
| `candidate-k215/k215.tm` | `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090` |
| `Lean/BusyBeaver/ZFC/KDense215.lean` | `b1ebe573ced4b336ead43dbe7278ad97c8d28c06412b43c7291d051b98c6395a` |
| `rocq/rocq-extension/coq/215/Table215.v` | `7bf3b9a5e37dadcb1091a8af0ccfc512e2704d7bd5f75cfb4563d42842d1d4a8` |

The exported `data/k215_transitions.json` contains all 430 transitions and these source hashes. Its SHA-256 in this audit is `880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755`. A second comparison confirmed that every exported transition agrees with both proof-assistant literals. The independently replayed 95,714-step bootstrap ends at state 83, head -8, with 95 one-cells; this finite prefix is a data-binding check, not evidence for the unbounded equivalence.

Both `blank_helical.py` and `count_blank_alphabet.py` import this exact-hash parser for their `--tm` input. Their receipt cannot silently describe a different 215-state machine. The latter independently enumerates the actual local predicate for all left/right pairs in thirteen center classes; its saved count is `38,256,607,897 * 439^4 = 1,420,903,358,357,108,792,377`. The saved cardinality receipt was reproduced exactly from the copied delivery code. Its SHA-256 is `8d419f3f842c5f934bfe71b46f6f06d0726f5bcbc3d0c5ead451d408871f6d2c`.

The fixed constant recipe uses that exact k. Its first window is S, `[438,438,438,434,435,436,0,1,188]`, and its second is E, `[0,438,0,0,437,438,0,437,0]`; the remaining center-valid windows are in lexicographic order. Both windows pass the center predicate. E fails the vertical propagation predicate at its predecessor in every possible global extension. Forbidding E therefore preserves every genuine computation tableau. The construction requires S at the origin, not unique S in the entire cyclic word. Only the chosen canonical completeness presentation has one S.

The direct K215 construction adds no stay-step prefix. Its fixed Start block is supplied by the machine's actual first transition, `0/0 -> write 1, move R, state 93`. Any prose inherited from an input-universal compiler that mentions a stay prefix or a unique End marker must be specialized accordingly.

## Reproducible finite checks

Run the following from the delivery package's top directory, replacing `/path/to/ProveIt` by a checkout at the pinned commit. The output paths below intentionally point to separate receipts. `count_blank_alphabet.py` and `blank_helical.py` take `--tm`, not `--repo`, and expect the original dense `.tm` file rather than its JSON export.

```sh
python code/verify_k215.py --repo upstream --output /tmp/k215_transitions.recheck.json
python code/blank_helical.py --tm upstream/Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm --output /tmp/blank_helical_checks.recheck.json
python code/count_blank_alphabet.py --tm upstream/Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm --output /tmp/blank_alphabet_cardinality.recheck.json
```

The archive includes the exact table at the upstream-relative path used in these commands. Do not pass `--formula-only` when reproducing the direct predicate enumeration. The three checker files inspected here have SHA-256 values:

| Checker | SHA-256 |
| --- | --- |
| `verify_k215.py` | `9d7b1d0238e2348c59b2d1d4fd33b8a9116793b4bfd2362362c1b81f5487e3e8` |
| `blank_helical.py` | `6f6ca0370faa612cde5136dfbd3d44f87e5e4694f2fefd3bdc77d84cf708d8f8` |
| `count_blank_alphabet.py` | `2837bebf8a5b71cb58e01c1bad7e142e1d2cdb6f7aa1011949974cba8fdd5589` |

These finite checks establish exact source identity and the finite compiler data claimed in their receipts. The universal tableau proof, the arithmetic compiler proof, and the existing K215 calibration proof remain separate mathematical obligations; no finite script run or checksum replaces them.

