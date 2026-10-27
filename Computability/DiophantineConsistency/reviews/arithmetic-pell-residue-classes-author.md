# Internal Pell residue classes: author validation

27 October 2026. complemented47_review authored and fully read the final
279-line `ArithmeticPellResidueClasses.lean`, 60-line Checks, executed driver,
and freeze script before their scoped execution. This is author validation,
awaiting independent review. No accepted source, umbrella, display, coefficient,
shared object, or Git state was changed.

The actual represented Pell sequence has base b+2 in an arbitrary IΣ1 model.
For internal `0<i≤n`, equality of x-coordinate residues modulo x(n) implies
`j%(4*n)=i` or `(j+i)%(4*n)=0`. The proof derives additive x-reflection,
antiperiodicity, strict growth and quarter reflection from the accepted actual
recurrence/norm/addition laws. Reduction of arbitrary internal j uses the
accepted represented Sigma1 period theorem and actual division/remainders.
There is no standard-natural index restriction, fundamental-unit oracle,
desired-index premise or new sequence definition.

The gap `2*x(n-1)<x(n)` is proved only for n≥2. In the local-window argument,
that premise follows from `0<i<n`; the zero-residue endpoint i=n needs no
gap. Hence base2,n1 is covered without the false strict bound there. Checks
also prove the real excluded collision at i0,j2,base2 modulo x1=2.

The signed doubled-index theorem retains `0<p` and `2*p≤m`, including
equality. The opposite-sign premise is a sum with residue zero, not a
truncated signed difference. Actual antiperiodicity turns it into an equality
at index2m+2t; the derived classes modulo4m descend modulo2m and cancel the
positive literal factor2. The output is `t%m=p%m` or `(t+p)%m=0`.
Applying the full classes at target/modulus index1 proves that divisibility
of x(j) by the base forces j%2=1, with witness j=2*(j/2)+1. Every subtraction
used in reflection and the local window has an explicit ordering proof.

The sole main import is frozen `ArithmeticPellPeriodicity`. Exact reuse is
99 custom modules,95 Foundation,384 cached artifacts,38 external boundaries
(including Init),114 boundary companions, zero prerequisite refresh. The
driver reauthenticates all planned pins, each current source header and the
exact reachable DAG, then all498 actual first artifact providers in its
explicit private LEAN_PATH. It rechecks1060 distinct observed paths after
the final pair. The cache's source/object/trace provenance is inherited from
the accepted plan; no new Foundation or external-package build is claimed.
I previously reviewed the Recurrence, Congruences and FirstNorm packets;
those roles do not make this new author validation an independent review.
Root supplied a read-only quarter-proof challenge, and controller supplied
an arithmetic/API challenge identifying the n1 exception and inclusive
doubled endpoint. Neither agent compiled this new leaf in this receipt.

Both final leaves pass under pinned Lean4.32, `-M6000 -j1 -DElab.async=false`,
one thread, fresh regular nonsymlink outputs and a512MiB reserve. Main8.023s
and Checks2.487s have peak RSS1816468/1800844KiB. The main log is empty;
all15 reports use only propext, Classical.choice and Quot.sound. Final free
space is1514745856bytes. Nothing is copied to the shared build directory.

All three attempts and complete sources/logs/commands/timings are retained:

1. Main failed after7.854s on API elaboration: addition-side orientation,
   model numeral normalization, lambda-form rewriting, one multiline
   application parse and one ambiguous lemma name. Checks did not execute.
2. Corrected main passed9.040s; Checks failed2.528s on explicit model-numeral
   normalization in the excluded-collision example. All main statements
   already passed, and its object is byte-identical to the final main.
3. Final pair passed cleanly. Only the example's numeral proof changed
   after attempt2. No mathematical statement, import, cap or scope changed.

The unexecuted attempt1 Checks input has the same source hash as attempt2's
retained Checks snapshot; the freeze script verifies this exact byte binding.
Historical source records retain their original live paths, with frozen
attempt snapshots providing the corresponding historical bytes.

| Module | Source SHA256 | Object SHA256 |
|---|---|---|
| ArithmeticPellResidueClasses | a6d523d2b60b8bd4098ab2b058dc8efff8af922f0dcd4b9c8b637b3a23c1e384 | 591e47a982c5b599b5b1c24ed28e1ff5b109907a2b3b8b90e7a5e512f0292a05 |
| ArithmeticPellResidueClassesChecks | 480cfe347c4f8cd585a036ddf74b5fc4637e96102c2c43793ae5312f600c79ff | f1850a5e4e0b2bbef4d5565a53e527e827c5bd14b52e5bdfff39e46c8ad88f29 |

Private provider: `/tmp/arithmetic-pell-residue-classes-author-lkbpmsmw/lib`.
The [complete replay packet](arithmetic-pell-residue-classes-replay.json) has
SHA256 `b578bdc2a2e77c0ce105e5e4efa81bd8ed5a10ba06cfd7586e26ffc75f7debac`.
Its final state is `9f72681ca3e76b42c64f985e6f6da6a7a5465b3135a3c1faebab359dadd01949`;
the executed driver is `4af666e94eaddf743e1390197daf4e81c8e6fcf4996b053921e2353c9834d373`.
The [durable evidence bundle](arithmetic-pell-residue-classes-author-replay/)
preserves all three attempts, authenticated inputs/providers, plan, proposal,
driver, freeze script and complete logs. The separate FILES manifest pins
the bundle, this receipt and replay packet.

This supplies the internal counterpart of the external doubled Pell
step-down and odd-index argument. Strong-norm integrality, Qh congruences,
actual p=R/2n=R+1 recovery, cofinal simultaneous witnesses and final PA/HA
carrier/equation assembly remain separate. No metric or equation claim is
introduced by this packet.
