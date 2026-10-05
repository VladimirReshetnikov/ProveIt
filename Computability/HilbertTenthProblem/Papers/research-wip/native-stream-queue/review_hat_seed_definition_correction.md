# Correction: finite atoms are not finite support in the hat-seed endpoint theorem

**Confirmed definition/hypothesis defect (W1), with an explicit counterexample.** The source's literal atom-count wording permits a nonatomic component. Under that reading its finite-public-seed exclusion is false. The intended theorem remains supported when the public seed is concentrated on a finite set with total probability one. Earlier reviews missed this distinction and must be qualified as below. The abstract's countable-support wording (W2) additionally needs its quantifier made explicit; it is not necessarily a second false theorem under a seed-of-our-choice interpretation.

The finding was recorded in the full body of placement commit `635a3e0266cec4426066aa96f0808720120b3323` and brought to this review by root. This independent proof challenge checks it against the original manuscript, supplies a nonempty-atom version of the counterexample, and retains the erroneous wording and earlier review statements. It does not edit or replace any frozen source/review.

## 1. Source and literal wording retained

Immutable arrival: `26e036956381b07bb43de0187965f8dcdf9194fb`.

Archive: `docs/incoming/hat_randomness_frontier.zip`,442,103 bytes, Git blob `5883bde6555a564be03a46bcc27358369cb92a2b`, SHA256 `eccc49ac838592997e1c7d8ef0c5ba7c1a95bd76abbb8f12814f552dc34b9e20`.

Member: `hat_randomness_frontier/hat_randomness_frontier.tex`,66,266 bytes,1660 lines, SHA256 `7d6c4815a4be0363a6d0deee1189396b4818033102ee28b21eb04b8102b47c71`.

Definition2.1, “Private and public randomness,” says at lines235-238:

> A finite-valued public seed has a finite set of possible values of positive probability. A countably supported public seed may have infinitely many such values.

Theorem6.5 (`thm:finite-public`), “Finite shared support does not attain cap one,” says at lines783-786:

> Let a public seed T have finite positive-probability support {t_1,...,t_s}, and let the private seeds be independent of one another, of T, and of the hats. If E Q_i<=1 for every i, then almost-sure positive divergence is impossible.

The distinction is between the finite set of atoms

`Atoms(T)={t:P(T=t)>0}`

and a finite set carrying the entire law. Finiteness of Atoms(T) does not imply `P(T in Atoms(T))=1`. A nonatomic law has no atoms; a mixed law can have one atom and a positive nonatomic remainder. Thus the literal condition supplied by the definition is too weak. If “finite support” is instead assigned its usual stronger probability-one meaning, the intended result is different and the defect is repaired; that stronger condition must be stated rather than silently substituted during review.

## 2. Explicit counterexamples, including one with a nonempty finite atom set

First let T be uniform on[0,1], independent of the hats and all private seeds. Then Atoms(T) is empty, hence finite. Define a measurable integer J by

```
J=0 on [0,1/2),
J=n on [1-2^(-n),1-2^(-(n+1))) for n>=1,
J=0 at the null endpoint T=1.
```

It has law `P(J=0)=1/2` and `P(J=n)=2^(-(n+1))` for n>=1. This is exactly the source's public endpoint law with p=1/2. Every player can compute this measurable coarsening of the available public seed; computation and external randomness are free in the stated query model. The source's Corollary9.4 (`cor:coarsening`) explicitly makes the same uniform-seed observation.

To avoid any convention that an enumerated finite support must be nonempty, use a mixed public law instead:

```
P(T=-1)=1/2,
conditional on T!=-1, T is uniform on[0,1].
```

Now Atoms(T) is exactly {-1}. Set J=0 at T=-1 and at the null endpoint1. On the continuous component put

```
J=n on [1-2^(-(n-1)),1-2^(-n)) for n>=1.
```

Each such interval has conditional probability2^(-n), so again `P(J=n)=2^(-(n+1))` and `P(J=0)=1/2`. There is one positive-probability public value, yet the same endpoint strategy is available. This law satisfies the finite atom-count condition even with s=1, and disproves Theorem6.5 under that literal condition.

Here is the relevant positive construction, so the counterexample is not just an appeal to an uninspected corollary. For m>=2 choose

```
alpha_m=P(J>=m)=2^(-m),
k_m=4^m,
L_m=ceil(4^(k_m)/m^2).
```

Each finite stage has L_m disjoint blocks of k_m pairs. In the potential strategy every T-role player guesses the opposite of its partner. An S-role player privately activates with probability alpha_m. If inactive it copies its partner. If active it inspects its partner and then the remaining visible hats until seeing a white hat or exhausting them; it departs from copying precisely when every visible hat is black. A complete block then loses only in the all-black configuration, with probability at most4^(-k_m), and gains one with probability `alpha_m*k_m*4^(-k_m)`.

The exact series satisfy

```
sum_m L_m*4^(-k_m) < infinity,
sum_m L_m*alpha_m*k_m*4^(-k_m)
 >= sum_m 2^m/m^2 = infinity.
```

Disjoint hats/private coins make the potential positive-block events independent. Borel-Cantelli gives only finitely many all-black blocks and infinitely many gain blocks almost surely. After the last bad block, complete-pair excess never decreases; an intermediate one-player prefix changes excess by only1/2. Thus the potential D_n tends to positive infinity at every physical prefix.

Actually disable stage m when J>=m, replacing it with constant zero-inspection guesses. J is finite almost surely, so only finitely many finite stages are disabled. This changes finitely many guesses on each such realization and preserves divergence. It does not require independence of the publicly gated gain events.

The enabling probability is1-alpha_m, independently of hats/private activation. The exact expected costs of players in stage m are

```
E Q_S=(1-alpha_m)[1+alpha_m(1-2^(-(2k_m-2)))]
     =1-alpha_m^2-alpha_m(1-alpha_m)2^(-(2k_m-2)) <1,
E Q_T=1-alpha_m<1.
```

Both tend to1, and every stage has players, so the uniform supremum is exactly1. All individual algorithms inspect finitely many hats. Therefore the counterexample satisfies the theorem's marginal cap, legal inspection model, independence assumptions and almost-sure success conclusion that the theorem purports to exclude. It uses neither a conditional cap at each seed outcome nor free hat inspections.

## 3. The missing premise in the finite-support proof and its repair

Let `a=sum_r p_r`, where p_r=P(T=t_r)>0 over the finitely many atoms. The proof defines

`z_i(U_i)=sum_r p_r*c_i(t_r,U_i)`.

Without a=1 its displayed expectation identity is false in general: the correct identity is

`E z_i = E[Q_i * 1_{T in {t_1,...,t_s}}]`,

not E Q_i. Also its centered equality must read

```
sum_(i<=n)(z_i-1)
 = sum_r p_r [sum_(i<=n)c_i(t_r,U_i)-n] -(1-a)n.
```

The omitted negative linear term prevents the asserted divergence. Finiteness of the number of atoms alone does not fix either step. The mixed-law example above has a=1/2.

The corrected hypothesis is explicit mass-one finite support:

```
there is a finite set {t_1,...,t_s} such that
P(T in {t_1,...,t_s})=1,
```

discarding any zero-mass listed values if necessary. Then sum_r p_r=1, both displayed steps are valid, and the reviewed weighted-cost/stopped-process proof applies. The correction does not require the cap to hold after conditioning on each public outcome. The independent-private exclusion and the finite weighted-sum argument under this corrected hypothesis are unaffected.

Likewise “countably supported” should mean concentration with probability one on a countable set when used in the prescribed-distribution theorem. Its proof explicitly uses that the union of its finite initial atom sets has probability one. Merely counting positive-probability singleton values is not a definition of concentration.

## 4. W2: preserve the abstract and distinguish its two readings

At abstract lines69-71 the source says:

> With a countably supported public seed and independent private randomness, the admissible caps are [1,infinity).

Taken to quantify over **every fixed** countably supported law, this is false: a deterministic seed is countably supported, and under the corrected finite-support theorem it cannot attain cap1. The abstract's next sentence about a fixed law correctly says attainment occurs exactly when its support is infinite.

Taken as a statement about the available class of seeds from which the strategy may choose, however, the sentence is true: that class contains an infinite-support seed. The main classification table at lines159-160 explicitly says “A countably supported public seed of our choice,” confirming a coherent existential interpretation. Consequently this review does not classify W2 as a separate unambiguous false theorem. It is a quantifier clarification.

Safe formulations are “with a public seed having countably infinite support” for the fixed-law assertion, or “with a suitably chosen countably supported public seed” for the available-class assertion. Preserve the original sentence and explain its scope; do not silently turn an existential class statement into a universal fixed-distribution claim.

## 5. Earlier review statements requiring qualification

The earlier bounded intake at commit18825ee16, `review_new_actions_26e036956.md`, SHA256 `55d864059205571c3eeab0d7522c72eaf7ea064c692fa9672dd10a7adc8b0a37`, read the model, finite-public argument and public endpoint spans. It reported “no defect identified in those inspected arguments” and “No new false claim requiring such a correction was identified in the declared scope.” Those assessments missed the finite-atoms versus mass-one-support distinction. They must now be read as corrected by this note. The separate commuting/atom-action review results and metadata checks are not affected.

The later `review_hat_endpoint_26e036956.md`, SHA256 `06141d33d913bb6815cc0b9b99ce49b41a6065e45d36bb17d14d29914b42233c`, opened with “No mathematical correction is requested” and concluded “No false or unproved step was identified within these endpoint arguments, so no source claim needs to be corrected or moved.” This was too broad for the literal Definition2.1. Its actual finite-public proof discussion used a genuine finite public support and an exhaustive weighted average. Its PASS is valid only after the probability-one concentration premise is made explicit. Its private endpoint and aggregate/stopping arguments are not refuted by this counterexample.

The subsequent `review_hat_placement_635a3e026.md`, SHA256 `2f5eca7fb3513fb1fdaef39ef14225b8fa08fd1ba5d62a51e1bdf0e8f5ae496d`, was explicitly a byte-placement audit with no new proof coverage. Its recorded human-read scope omitted the full commit body, where W1 and W2 had been recorded. Its byte-equality findings remain valid; its inherited endpoint summary must carry the qualification above. This is not a retroactive claim that the omitted body had been reviewed.

All these frozen records should remain available. Under the incoming retention rule, the original defective wording and the uniform or mixed-law counterexample belong in an attributed numbered correction remark when the article is written. The corrected mass-one theorem can be stated alongside it. No source or review history should be silently erased. The placement commit remains ancillary-only, so this review does not claim that the planned manuscript correction has already been implemented in the host article.

## 6. Exact bounded read scope and limits

New source reads for this proof challenge, with inclusive line numbers and SHA256 of the LF-normalized span including its final newline:

| Original TeX span | Content | SHA256 |
|---|---|---|
| 57-89 | Full abstract | bd5deb23e79ae5e0cf13b67365fdf1b541ec4ee7f5a5cf8c1ec7cb192a1bbf83 |
| 138-163 | Cap convention and classification table | 4835cfadbccd3abfb787097813075ebc533675f70b7df7c047526fad1c2c7fb9 |
| 193-262 | Complete model/Definition2.1 and fairness conventions | b66b6568babc10bc47f42c7738c23b77ca3319cf8056f15833635662c59e39c6 |
| 779-822 | Theorem6.5 and its complete proof | a8afa846214af7b60214ff79da5121040c84bda485f2df43cdcc8e10826482fb |
| 823-1038 | Finite block, cost, scheduling/deletion and adjacent upper constructions | 9fdb56b6673ab187efc74ab2bc30e9d73f299b41b558c691512ed83f11115b4c |
| 1039-1208 | Public endpoint, entropy, fixed-support classification and Corollary9.4 | f71dd6c07748dea6f3baeddd8590955c0bc26f61b14c84ebc7f1eca89b7f89ae |

The full58-line placement commit message was read; SHA256 of `git show --format=%B --no-patch 635a3e026` is `210c3761ba0ee512eabbdd042892dfb9c6709494cde2b279c8ccef43ffaeb397`. The three earlier review notes were read in full (75,88 and44 lines respectively), with their pins above. The incoming retention rule at lines426-440 was also reread. These are precise proof and attribution reads, not a full new manuscript review.

No supplied, archived, committed, frozen or copied helper, verifier or builder was executed or imported. No fresh mathematical test program was run: the counterexample and cost/divergence proof are the written argument above. Git/archive reading and hashing were metadata operations only. No PDF was built or rendered, no external literature was audited, and no repository file was changed. The corrected distinction concerns public-randomness hypotheses and hat-query cost; it supplies no paid ordinary-integer arithmetic compiler or operation-count saving.
