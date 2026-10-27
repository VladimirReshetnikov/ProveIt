# Internal Pell residue classes: independent ROOT review

27 October 2026. Accepted after full review of the final 279-line main,
60-line Checks, author driver and freeze script, and an independent fresh
two-leaf replay. Both compiled objects and complete logs match the author.
The scope is an arithmetic component of the internal consistency argument;
the displayed equation's PA/HA equivalence remains open.

In every IΣ1 model, for the represented Pell sequence with base b+2 and
arbitrary internal indices 0<i≤n, equal x-coordinate residues modulo x(n)
imply j%(4n)=i or (j+i)%(4n)=0. The proof derives x-reflection and
antiperiodicity from the accepted addition laws, reduces j by the represented
period theorem, and excludes the other local quarter using strict growth.
It uses no supplied carrier index, standard-natural restriction or new
fundamental-unit premise.

The strict gap 2*x(n-1)<x(n) is used only after deriving n≥2 from 0<i<n.
The i=n endpoint and base2,n1 case therefore remain valid. Checks also
exhibit the excluded target0 collision at base2: x(0) and x(2) both have
residue1 modulo x(1)=2. All reflected natural subtractions have explicit
ordering justifications.

The signed doubled step retains the inclusive hypothesis 0<p and 2p≤m.
An opposite-sign input is represented by a sum having residue zero.
Antiperiodicity converts it to an equality at index2m+2t; reduction modulo2m
and cancellation of the positive factor2 give t%m=p%m or (t+p)%m=0.
At target/modulus index1, divisibility of x(j) by the base implies j%2=1
and the actual internal witness j=2*(j/2)+1.

ROOT reauthenticated the frozen author packet, all38 manifest entries,
all three historical attempts and their immutable source/driver snapshots.
The first author main failed on arithmetic API elaboration and parsing;
the second main passed and its Checks failed on model-numeral normalization.
The third author pair passed. Historical bytes, commands, complete diagnostics
and timings are retained; no unsuccessful result is counted as a proof.

Exact cache reuse is99 custom modules,95 Foundation,384 artifacts and38
package boundaries with114 current companion observations, zero refresh.
The independent driver rereads current import headers, verifies the exact
reachable DAG and all498 actual first artifact providers in its private
LEAN_PATH. Its2,978 hash comparisons cover1,110 distinct observed paths,
including a final recheck. Historical provenance and companion qualifications
are inherited from the accepted plan; no dependency rebuild is claimed.

Pinned Lean4.32 runs with -M6000 -j1 -DElab.async=false, one thread, fresh
regular outputs and a512MiB reserve. Independent main8.197s/Checks2.465s
have peak RSS1,814,532/1,798,988KiB. The main log is empty; all15 complete
axiom reports contain only propext, Classical.choice and Quot.sound.
ROOT needed one clean pair and no source changes. Final free space was
1,485,197,312bytes; nothing was copied into the shared build directory.

| Module | Source SHA256 | Object SHA256 |
|---|---|---|
| ArithmeticPellResidueClasses | a6d523d2b60b8bd4098ab2b058dc8efff8af922f0dcd4b9c8b637b3a23c1e384 | 591e47a982c5b599b5b1c24ed28e1ff5b109907a2b3b8b90e7a5e512f0292a05 |
| ArithmeticPellResidueClassesChecks | 480cfe347c4f8cd585a036ddf74b5fc4637e96102c2c43793ae5312f600c79ff | f1850a5e4e0b2bbef4d5565a53e527e827c5bd14b52e5bdfff39e46c8ad88f29 |

Accepted independent provider:
`/tmp/arithmetic-pell-residue-classes-root-er_y8ywe/lib`.
The [ROOT replay packet](arithmetic-pell-residue-classes-root-replay.json)
and [durable bundle](arithmetic-pell-residue-classes-root-replay/) preserve
the driver, exact inputs/providers, sources, commands, complete logs and
timings. Its FILES manifest also pins this receipt and replay packet.
The [author packet](arithmetic-pell-residue-classes-replay.json) retains all
three attempts under its separate38-file manifest.

Strong-norm integrality, Qh congruences, actual first/main index recovery,
cofinal simultaneous witnesses and final PA-to-HA assembly still remain.
The base10 display and all equation coefficients and metrics are unchanged.
