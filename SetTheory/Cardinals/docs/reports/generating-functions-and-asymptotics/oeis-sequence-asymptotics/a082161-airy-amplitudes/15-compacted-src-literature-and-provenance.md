# A254789 source check and scope

Checked 2 October 2026, using public primary sources and read-only GitHub search. This is a bounded novelty check, not proof that no relevant result exists anywhere.

## Primary source

Andrew Elvey Price, Wenjie Fang, Michael Wallner, *Compacted binary trees admit a stretched exponential*, https://arxiv.org/abs/1908.11181 (preprint 2019; journal publication 2021), PDF https://arxiv.org/pdf/1908.11181.

- Proposition 2.11 gives the signed two-parameter compacted recurrence
- Definition 2.12 gives the equinumerous H-decorated paths that forbid equal labels greater than one in an HHV pattern
- Theorem 1.1 proves c_n=Theta(n!4^n exp(3 z n^(1/3)) n^(3/4))
- Section 3.4 explicitly describes the amplitude and full expansion as conjectural; its numerical amplitude fit is 173.12670485

Those are the precise known inputs and motivation. A full-equivalent proof must not be inferred from the published theta estimate.

## Later primary work checked

Manosij Ghosh Dastidar and Michael Wallner, *Asymptotics of relaxed k-ary trees*, AofA 2024, https://arxiv.org/abs/2404.08415 and https://arxiv.org/html/2404.08415v1.

Its stated asymptotic main theorem remains a theta estimate for relaxed k-ary trees. Proposition 10 gives compacted k-ary recurrences, specializing to the recurrence above when k=2. It does not state an unrestricted binary compacted amplitude theorem.

The earlier bounded-right-height problem is different: Antoine Genitrini, Bernhard Gittenberger, Manuel Kauers, Michael Wallner, *Asymptotic enumeration of compacted binary trees of bounded right height*, https://arxiv.org/abs/1703.10031. Its asymptotic equivalents do not resolve the unbounded-height amplitude.

Michael Wallner's current project bibliography was also checked: https://dmg.tuwien.ac.at/mwallner/stretched-exponentials/. Targeted searches for the exact sequence ID, compacted binary asymptotics, and the amplitude constant found no later unrestricted compacted amplitude resolution.

## ProveIt repository check

Repository: https://github.com/VladimirReshetnikov/ProveIt.

Read-only default-branch code searches returned:

- `A254789`: no hits
- `compacted`: one unrelated prose hit, concerning a compacted table of contents in `SetTheory/Cardinals/docs/reports/enumerative-combinatorics/reverse-reply-avoidance-game/notes/build_and_validation.md` at commit 89daa64f832d2a5f2113db37b2c9fbcd9f6cfa24

This supports continuing the problem but is not a guarantee of unpublished novelty. No repository writes, issue comments, uploads, or bulk repository downloads were performed.

## Numbering

The mathematical sequence c_n counts n internal nodes, with c_0=1 and c_1=1. Its beginning is 1,1,3,15,111,1119,... . The current OEIS entry https://oeis.org/A254789/internal was checked directly: its offset is 0, its explicit formula identifies a(n)=c(n,n), and its asymptotic field still states the theta result. Thus the mathematical indexing used here agrees with the current OEIS indexing; no index shift is needed.
