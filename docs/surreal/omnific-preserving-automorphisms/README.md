# Omnific-Preserving Automorphisms

**Convex-scale stabilizers, definable constants, nondefinable monomials, and algebraic-parameter rigidity**
Merged research report from four manuscripts written independently and dated
23 September 2026 (items 02, 04, 08 and 09 of batch 26, placed in `f4c9504`;
they keep those numbers here). Prepared for Vladimir Reshetnikov.

```
article.tex                                 the report, standalone LaTeX with an internal bibliography
article.pdf                                 the compiled report, 45 pages
README.md                                   this guide
02-parameter-rigidity-source_audit.md       source 02's source and novelty audit, as delivered
04-preserving-automorphisms-source_audit.md source 04's source and claim audit, as delivered
code/
  09-omnific-preserving-verify_finite_identities.py   source 09 checks (standard library; prints only)
  09-omnific-preserving-Makefile                      source 09's build/check targets (delivered
                                                      file names; they do not build this report)
  04-preserving-automorphisms-verification.py         source 04 checks (SymPy; writes a JSON report)
  04-preserving-automorphisms-build.sh                source 04's build script (compiles its own
                                                      omnific_automorphisms.tex; not this report)
  08-integer-part-symmetries-verify.py                source 08 checks (standard library; always
                                                      writes verification.json beside itself)
  02-parameter-rigidity-verify.py                     source 02 checks (standard library; writes
                                                      verification.json beside itself by default)
  02-parameter-rigidity-Makefile                      source 02's build/check targets (delivered
                                                      file names; they do not build this report)
data/
  09-omnific-preserving-verification_output.txt       source 09's recorded run
  04-preserving-automorphisms-verification_report.json  source 04's recorded run (7,062 assertions)
  04-preserving-automorphisms-requirements.txt        pins sympy==1.14.0
  04-preserving-automorphisms-build_audit.json        source 04's build record for its own PDF
  08-integer-part-symmetries-verification.json        source 08's recorded run (9,469 checks)
  02-parameter-rigidity-verification.json             source 02's recorded run (7,041 assertions)
  02-parameter-rigidity-build_audit.json              source 02's build record, with SHA-256 hashes
                                                      of its delivered files
```

Every label in `article.tex` carries the prefix `opa:` (146 labels). Source
02's part carries the sub-prefix `opa:par:` (43 labels). These prefixed labels identify the assembled report; the earlier placed
base used source-local labels. No implementation mapping in the [formalization ledger](../../FORMALIZATION.md)
cites an `opa:` label, and there is no Lean code about omnific integers in
the repository.

## Four sources, one report

| | Manuscript | Repository pin | Contributes |
|---|---|---|---|
| **09** | *Omnific-Preserving Automorphisms: convex-scale stabilizers, definable constants, and nondefinable monomials* | `fb5c4b5` | The base text and structure. The criterion for any characteristic-zero `k` and any unital coefficient ring (Theorem 3.3, with 04's proof) and its derivation form (Theorem 3.4). The operator form (Corollary 3.5), the rank dichotomy (Theorem 4.13) and the strong factorization (Theorem 5.1). The finite-rank derived-length bound `r−1` (Theorem 6.3), sharp for `Q^r` also for the abstract group (Theorem 6.6). The `R^κ` actions and nonsolvable stabilizers (Theorems 7.6, 7.7). Set-parameter nondefinability (Theorem 9.1), and no definable valuation-representative rule (Theorem 9.4). The projections and truncation (Theorem 8.2). Files prefixed `09-omnific-preserving-`. |
| **04** | *Automorphisms Preserving the Omnific Integers: a convex-support criterion, fixed fields, and nondefinability of Conway monomials* | `fb5c4b5` | The import-free proof of the criterion through the logarithmic character, which is the proof of record for `No` (Theorem 3.3). Exact displacement (Theorem 4.2) and the common-shift exponential–logarithm correspondence (Theorems 4.7, 4.8). The bottom-subgroup fixed field (Theorem 4.15), separation, and the relative Hahn hull (Theorem 7.4, Corollary 7.5). The commutator formula (Theorem 6.8). The one-term class and the `RV` sort (Remark 9.5). The real axis inside the leading-term kernel (Theorem 10.2). Files prefixed `04-preserving-automorphisms-`. |
| **08** | *What the Omnific Integer Part Remembers: coefficient reconstruction, convex-scale automorphisms, nondefinable monomials, and an explicit wreath product* | `befe739` | The divisibility-free threshold for single flows (Theorem 4.10) and phase shears (Theorem 4.17). The faithful `Z ≀ Z` with exact commutator leading terms (Theorems 6.8, 6.10). The order formula on `Oz` (Lemma 8.1) and the floor map (Theorem 8.2). The wild coefficient lift (Proposition 10.3) and the Gaussian fixed field `Q` (Corollary 10.4). Files prefixed `08-integer-part-symmetries-`. |
| **02** | *Algebraic-Parameter Rigidity of the Omnific Integers: strong cancellation, finite-type embeddings, and nonalgebraizable formal flows* | `fb5c4b5` | All of Part II (Sections 12–19). Files prefixed `02-parameter-rigidity-`. |

`fb5c4b5` is 12 commits before the placement `f4c9504` and `befe739` is 10
commits before it. Both pins contain the batch-24 placement `be06fc8`. Neither
contains the reconstruction section that batch 25 added to the omnific
Diophantine report. The source manuscripts are not shipped: no delivered
`.tex`, PDF or README is here. Their code, recorded data, build records, and the
source audits of 02 and 04 are shipped. The hashes in
`data/02-parameter-rigidity-build_audit.json` refer to 02's delivered files
(`article.tex`, `article.pdf`, `README.md` and others under their delivered
names). Most of those files are not shipped. The theorem numbers in
`04-preserving-automorphisms-source_audit.md` are those of manuscript 04: its
Theorem 4.3 is Theorem 3.3 here, and its Theorem 8.1 is Theorem 7.4.

**Why one report.** 04, 08 and 09 prove one classification at three
generalities, with the same consequences:

- rank triviality;
- fixed field `R`;
- set-parameter nondefinability of monomials;
- a non-nilpotent stabilizer.

The shared results are printed once. 09 is the base because its hypotheses on
`(k, 𝔬)` are the weakest and its group-theoretic results the widest. 04's
proof is used for the criterion because it imports no correspondence. 08's
single-flow threshold is kept as a marked case because it needs no
divisibility. 02 has a different subject: algebraic families of embeddings,
not automorphisms. It is the shift-zero complement of Part I and forms Part
II. None of the four contradicts another or any report in the collection.

**Printed once.**

- **The criterion** (04, 09; 08 for single flows): Theorem 3.3 with Theorem
  3.4, Corollary 3.5 and Theorem 4.10. 04's logarithmic-character coefficients
  `a_{σ,δ}` and 09's operator coefficients `c_δ` are **different functionals**.
  Example 3.2 has `a_{σ,ω+1}(ω²) = 1/2` while `c_{ω+1}(ω²) = 0`. Each
  vanishing condition is equivalent to preserving the integer part, so the
  two conditions are equivalent.
- **Rank dichotomy** (Theorem 4.13).
- **Fixed field `R`** (Theorem 7.2).
- **Set-parameter nondefinability** (Theorem 9.1).
- **One group**: 04's `⟨A_s, B_u⟩` and 08's `⟨A_1, B_1⟩` are the same group at
  `s = u = −1` (Theorems 6.8, 6.10).
- **Strong factorization** (Theorem 5.1).

**Cited, not reprinted.** 04, 08 and 09 each reprove parts of the omnific
Diophantine report (`odg:`), which gained this material after their pins:

- units and constant products;
- Pell rigidity;
- `Frac Oz = No`;
- the multiplier ring and the reconstruction of `R`, order and standard part;
- automorphisms of `Oz` fix `R`;
- the split restriction to `Aut C`;
- the definitions of `Z`, `Π` and `C`.

08's formula for `Π` is `odg:cor:definablect` in structure, and that
corollary was in the tree at 08's pin. Both 08's and 09's formulas are
dominated by the one-witness `∃y x² = 2y²` of `odg:def:thm:ideal`. Only the
extras are printed:

- the order formula on `Oz`;
- the projections `P_−, P_0, P_+` on all of `No`;
- the floor map;
- truncation at a named monomial;
- the set-sized version;
- the Gaussian fixed field `Q`;
- the wild lift.

**Kept as second routes.**

- 04's proved exponential–logarithm correspondence on common positive shifts
  (Theorem 4.8), beside the imported one.
- 04's separation lemma, beside the explicit functional in Theorem 7.2.

**Added by the merge**, each tagged `[merge]` with a complete proof:

- the combined Theorem 3.3 (09's generality, 04's proof, and 09's first step,
  which removes 04's use of `⋂ n𝔬 = 0`);
- Example 3.2;
- Remark 6.11 (`⟨A_s, B_u⟩ ≅ Z ≀ Z` for all real `s, u ≠ 0`);
- Question 11.6.

**Notation.**

- Part I uses the small-`t` convention `t^γ = ω^{−γ}` of 04 and 09, so the
  purely infinite ideal `Π` sits at **negative** `t`-exponents. 08's
  `ω`-convention statements are translated: its `D_{φ,δ}` is `D_{δ,−φ}`.
- Part II keeps 02's large-monomial convention `X^g = ω^g`, which is that of
  the other omnific reports.
- `Π` replaces `𝒥` (08, 09) and `𝓘` (04).
- `𝒜_k = k ⊕ Π` replaces 09's `B`, 04's `𝒜` and 08's `𝓑_k`.
- `ℛ_𝔬 = 𝔬 ⊕ Π` replaces `A_D`, `O_D`, `A_k` and `R_Γ(D, k)`. The coefficient
  ring `D` is renamed `𝔬` because `D` names derivations.
- `C_δ` replaces 08's `H_δ`; in Part II 02's `H(a)` is `C(a)`, the
  transcendence report's notation. The quotient report's `H_a` means the
  opposite.
- `q_β` is the exponent-coefficient functional, for 09's `q_η`, 08's `c_a`
  and 02's `χ_b`.
- 09's parameter monomial `H = ω^η` is `η = ω^β`.

Section 1.5 and Appendix A.4 list every renaming.

## What the report claims

Part I (`K = k((t^Γ))`, `k` of characteristic zero, `Γ ≠ 0` divisible, `𝔬 ⊆ k`
unital):

- **Theorem 3.3** (convex-support criterion). A strong `k`-linear
  1-automorphism `σ` preserves `ℛ_𝔬` if and only if
  `a_{σ,δ}(C_δ) = 0` for every `δ > 0`, if and only if `σ` commutes with
  `P_−, P_0, P_+`. Four further equivalent conditions are listed. The
  stabilizer does not depend on `𝔬`. The proof is elementwise, imports no
  exponential–logarithm correspondence, and holds for `Γ = No`, that is for
  `Oz` and `Oz[i]`.
- **Theorem 3.4 and Corollary 3.5.** A contracting strong derivation preserves
  `𝒜_k` if and only if `c_δ(C_δ) = 0`. `U = Exp(𝔏_A)` holds for set-sized
  `Γ`. For `No` it holds granted the proper-class correspondence (see below)
  or on the common-shift class (Theorem 4.8).
- **Theorems 4.1, 4.2 and 4.8.** Homogeneous shears
  `t^γ ↦ t^γ exp(θ(γ) t^δ)` with `θ(C_δ) = 0`, their exact first
  displacement and fixed field `k((t^{ker θ}))`, and the proved correspondence
  on common positive shifts.
- **Theorem 4.10** (08). For any ordered abelian group, divisible or not, a
  single flow `exp(s D_{δ,θ})` preserves `ℛ_Z` if and only if
  `θ(C_δ) = 0`. `θ(δ) ≠ 0` is allowed.
- **Theorem 4.13.** The stabilizer is trivial if and only if `Γ` is
  Archimedean.
- **Theorem 4.15.** Its fixed field is `k((t^{B(Γ)}))`, where `B(Γ)` is the
  bottom convex subgroup. **Theorem 4.17**: phase shears.
- **Theorem 5.1 and Corollary 5.2.** The strong `Oz`-stabilizer is
  `{M_{χ,τ}} ⋉ U_Oz`. Every field automorphism preserving `Oz`, strong or
  not, fixes `R` and commutes with the projections and the floor.
- **Theorems 6.3 and 6.6.** In finite ordered rank `r` the derived length is
  at most `r − 1`. It equals `r − 1` for `Q^r`, for the Lie algebra and for
  the abstract group.
- **Theorems 6.8 and 6.10.** Exact commutators. `⟨A_{−1}, B_{−1}⟩ ≅ Z ≀ Z`
  faithfully, with leading terms `(−1)^n ω^{ω²−ω−n}`.
- **Corollary 6.12.** Every set stabilizer contains `Z ≀ Z`.
- **Theorem 7.2.** `Fix U_Oz = R`, also for all field automorphisms of `No`
  preserving `Oz`. The common fixed subring of all ring automorphisms of
  `Oz` is `Z`.
- **Theorem 7.4 and Corollary 7.5.** Elementary shears fixing a set `A` have
  fixed field `k((t^{V_A}))`. For monomial parameters this is the fixed field
  of the full stabilizer.
- **Theorems 7.6 and 7.7.** Faithful `R^κ` actions fixing any set of
  parameters, and nonsolvable set stabilizers.
- **Lemma 8.1 and Theorem 8.2.** `z ≥ 0 ⇔ ∃a,b (b ≠ 0 ∧ a² = z b²)` on `Oz`.
  `P_−, P_0, P_+` on all of `No`, the floor map, and truncation at a named
  monomial are definable in `(No, Oz)`.
- **Theorem 9.1, Corollary 9.2 and Theorem 9.4.** For every set of parameters,
  neither the monomial class nor the omega-map is definable, not even in the
  pure ring `Oz` for the monomials in `Oz`. No valuation-representative rule is
  definable.
- **Remark 9.5.** The one-term class and the `RV` sort.
- **Theorems 10.1 and 10.2, Proposition 10.3, Corollary 10.4.** Gaussian
  results:
  - conjugation-compatible witnesses;
  - an imaginary-time shear that fixes any set and moves the real axis inside
    the leading-term kernel;
  - a wild coefficient lift that moves an ordinary real;
  - the common fixed field of all `Oz[i]`-preserving automorphisms is `Q`.

Part II (source 02):

- **Theorem 13.1 and Corollary 13.3.** `ℛ_𝔬(k, Γ)` has every nonzero element
  dividing a positive monomial if and only if `Γ` has no order unit. This is
  `bst:thm:fieldcriterion` restricted to positive support. `Oz` and `Oz[i]`
  are root-covered.
- **Theorems 14.4 and 14.5.** Embeddings of a set-sized root-covered domain
  into a finite-type domain land in a finite field of algebraic constants.
  There is a pointed version.
- **Theorems 15.1, 15.3, 15.4 and 15.5.** Polynomial and Laurent coefficient
  rigidity. Strong cancellation: every isomorphism `Oz[X_1..X_n] ≅ B[Y_1..Y_n]`
  carries `Oz` onto `B`. Automorphisms of `R[T]` and `R[U^±]`.
- **Theorem 16.2 and Corollary 16.3.** `ML(Oz[T_1..T_n]) = Oz`. There are no
  finite-rank additive or torus coactions and no gradings.
- **Theorems 17.2, 17.3 and 17.5.** Formal flows of all orders that no
  polynomial family realizes, even to first order. The monomial orbit field
  has transcendence degree `dim_Q χ(Γ)` and is never finitely generated.
- **Theorem 17.6.** The commuting derivations `D_b` are `osq:prop:classder`.
  They are independent over `Oz`. **Corollary 17.9**: a continuum of
  independent orbit elements.
- **Proposition 18.1.** The bounded-scale fraction field of a set-sized
  workspace, as in `bst:prop:localdensity`.

## What the report does not claim

Appendix B lists every source's non-claims: 13 from 09, 13 from 04, 12 from 08
and 11 from 02. In brief:

- No classification of nonstrong automorphisms of `(No, Oz)` or of `Oz`.
- Strongness of `Oz`-preserving automorphisms is not shown.
- No construction for arbitrary logarithmic characters.
- No generation or density theorem.
- The relative fixed field is computed for elementary shears only, and for
  monomial parameters. The Hahn hull is not definable closure.
- The shears are not exponential and do not respect the omega-map.
- Nothing is claimed after naming a proper class of parameters. Bare
  nondefinability of coefficient-one monomials already follows from character
  twists.
- No set or class of all class automorphisms is formed.
- Part II:
  - its theorems need injectivity and domain targets;
  - root-covered is sufficient, not necessary;
  - the formal flows are not convergent and not internal exponentials;
  - no classification of `Aut(Oz)` or of all derivations;
  - no Jacobian or general cancellation claim.
- No named conjecture is solved. The report is not refereed, has no Lean
  formalization and makes no priority claim. The finite checks test identities
  only.

**The imported correspondence.** The correspondence between contracting strong
derivations and strong 1-automorphisms is Cited theorem 1.1 (BKKPS Theorem
3.13). BKKPS proves it for set-sized `Γ`. The placement dossier doubted 09's
citation of Kaplan–Krapp–Serra Fact 4.2 for the surreal case. The merge re-read
the arXiv v3 PDF: Fact 4.2 does state the bijection, and says that it "also
holds for G a proper class", without a separate proof (Remark 1.2). So these
statements depend on that assertion for `Γ = No`, and say so:

- `U_Oz = Exp(𝔏_A)` (Corollary 3.5);
- the group upper bounds (Theorem 6.3);
- the "exactly `r − 1`" in Theorem 7.7.

Theorem 3.3, the explicit constructions on `No` and nonsolvability do not
depend on it.

## Open questions, re-scoped

- **Questions 11.1–11.6.**
  - 11.1: strongness of `Oz`-automorphisms (04 and 09).
  - 11.2: admissible logarithmic characters (04).
  - 11.3: full relative fixed fields (04).
  - 11.4: generation and exhaustion (04 Q4 with 08 Q1).
  - 11.5: normal-form data weaker than the omega-map (08).
  - 11.6: the criterion for non-divisible `Γ` (merge).
- **08's Question 2** asked whether `C` is first-order reconstructible from
  the pure ring `Oz[i]`. It is **answered** by `odg:def:cor:internal`, and
  independently by 09's Pell-divisibility route, so it is dropped.
- **02's questions** are 19.1–19.3. Question 19.2, on formal directions, is
  **partly answered** by Part I: positive-shift derivations preserving `Oz`
  are classified, and those with a common shift set integrate to automorphisms
  inside `No`. The shift-zero and other cases stay open.

Questions of other reports (Section 11.1). These are recorded here only; the
other reports were not edited.

- **`osq:q:invisible`**, second clause ("How much can an automorphism of `Oz`
  do inside `Π` while fixing `ct`?"): **partly answered** for strong
  automorphisms. The nonstrong case and the first clause stay open.
- **`odg:def:q:realform`**: **negative information** only (Theorem 10.2,
  Proposition 10.3). It is not answered.
- **The surcomplex report's "effective descriptions inside the leading-term
  kernel"** (`saut:sec:questions`): **not answered**. Its `Oz`-stabilizing part
  is described. No exhaustion theorem is proved.

## Stale statements corrected

Appendix A.3 records these.

- **09's divisibility remark** was right for `𝒜_k` and wrong for the integer
  part: the translation sends `t^{−1}/2 ∈ Z + t^{−1}R[t^{−1}]` outside it
  (Remark 4.11).
- **The reconstruction and definability sections of 04, 08 and 09** were
  written before the Diophantine report's reconstruction section was placed.
  They are cited. 04's remark that its reconstruction is not first order is
  superseded.
- **Credits added:**
  - `saut:thm:shiftflow`, which 08 and 09 did not credit;
  - `saut:thm:decomp`;
  - the rigidity report's `thm:no` and `cor:question54`, where 09 cited only
    KKS Proposition 5.2;
  - for 02: `bst:thm:fieldcriterion`, `bst:prop:localdensity`,
    `osq:prop:classder` and `odg:thm:fractions`.
- **The surcomplex report's `T_1(t) = t/(1−t)`** does not preserve `Oz`
  (Example 4.12).
- **Checked true:**
  - "the catalogue lists 51 reports", at the pins;
  - the antecedents in `saut` and `odg` that the sources name;
  - no report contained an `Oz`-automorphism classification.

## Relation to the neighbouring reports

- [`omnific-diophantine-geometry`](../omnific-diophantine-geometry/) (`odg:`).
  - Its reconstruction section (`odg:def:`) is the source of everything that
    this report cites about what `Oz` remembers.
  - This report adds the automorphisms and the nondefinability, and records
    negative information for `odg:def:q:realform`.
- [`set-sized-quotients-of-omnific-integers`](../set-sized-quotients-of-omnific-integers/)
  (`osq:`).
  - Its `osq:q:invisible` is partly answered.
  - Its `osq:prop:classder` derivations are Part II's `D_b`.
  - Its `osq:thm:derivations` (derivations into set-sized modules vanish) is
    consistent with them.
- [`surcomplex-field-automorphisms`](../../surcomplex/surcomplex-field-automorphisms/)
  (`saut:`).
  - Fixed-shift flows, the four-layer decomposition and the phase twists come
    from this report.
  - This report describes the `Oz`-stabilizing part of its kernel `U`.
- [`exponential-automorphism-rigidity`](../exponential-automorphism-rigidity/).
  Every exponential 1-automorphism of `No` is the identity, so the shears are
  not exponential.
- [`single-dilation-hahn-support`](../../surcomplex/single-dilation-hahn-support/)
  (`dsup:`). The dilation `S_2` defines the monomials, and `(No, Oz)` does
  not.
- [`transcendence-over-bounded-support`](../transcendence-over-bounded-support/)
  (`bst:`). Its field criterion underlies Theorem 13.1.
- [`omnific-groups-and-lattices`](../omnific-groups-and-lattices/). It is a
  sibling report written concurrently from the same batch.

## What was run

For this merge all four suites were rerun on copies, with Python 3.14.4 and
SymPy 1.14.0. Each reproduced its recorded result:

| Suite | Result |
|---|---|
| 09 | twelve PASS lines and `ALL CHECKS PASSED` |
| 04 | 7,062 assertions in 17 groups, `all_checks_passed` |
| 08 | 9,469 checks in 15 categories, `PASS`; the rewritten file is identical to the shipped record up to line endings |
| 02 | 7,041 assertions in 13 families, `PASS`; identical up to line endings |

The placement dossiers ran further independent checks, which are not shipped:

- 281 for 04, 08 and 09, including Example 3.2, the commutator formula for
  symbolic `s, u` and the failure example of Remark 4.11;
- for 02, the quotient-rule identity of Example 17.8, to 29 terms.

## Build and reproduce

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build uses standard packages only and gives no errors, warnings,
overfull or underfull boxes, or undefined references. Build in a scratch
directory; the auxiliary files are not kept here.

Three of the shipped scripts write files, so rerun the checks on a copy:

```
mkdir opa-checks && cp code/*.py opa-checks/ && cd opa-checks
python 09-omnific-preserving-verify_finite_identities.py            # prints only
python 04-preserving-automorphisms-verification.py --output rerun-04.json   # needs sympy==1.14.0
python 08-integer-part-symmetries-verify.py                         # writes verification.json here
python 02-parameter-rigidity-verify.py --output rerun-02.json
```

The scripts write as follows:

- Without `--output`, 04's script writes `verification_report.json` into the
  current directory.
- 08's script always writes `verification.json` next to itself.
- 02's script does the same unless `--output` is given.

The two Makefiles and `04-preserving-automorphisms-build.sh` are shipped as
delivered. They name the manuscripts' own files (`omnific_automorphisms.tex`,
`article.tex`, `verify.py`, `verify_finite_identities.py`), which are not
present here under those names, so they do not run as-is.
