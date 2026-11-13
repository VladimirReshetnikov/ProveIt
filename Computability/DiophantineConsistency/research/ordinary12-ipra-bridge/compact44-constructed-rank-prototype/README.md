# Compact symbolic rank forced by a packing

`CompactConstructedRank.rank_properties` proves the population, phase and
size conditions used by the outer Pell construction, in an arbitrary model of
`IΣ₁`. Its input is a `PackingInput` for width 590069 and the **symbolic**
compact low and high masks, together with the two explicit premises
`(Cw 590069 N X - 1) % 4 = 0` and `low % 4 = 2`. Define
`q = Exp.exp (590069*N)`, `β = Exp.exp 590069 - 1`,
`J = rep 590069 N`, and

```
R = ((q - 1) * (q - Fw 590069 K N s X)
     + alpha 590069 K N s X) * (q^2 - 1)
    + (low + q * (high + β)) * J.
```

The conclusion is `population R = 3*(590069*N) + 2`, `R % 4 = 3`, and
`2*(590069*N) < R`. The mask populations are 589083 and 986, and their sum
is exactly 590069. The proof uses the compact masks' established bounds,
low evenness, high mod-eight residue and these populations, together with
the generic `ArithmeticRankForcing` and `ArithmeticMaskPopulation` results.
It uses no 2011-specific masks or widths. The kernel is an arbitrary `K`;
the statement applies to the actual kernel after instantiating it. The
rank's precise `c` parameter is `(low + q*(high+β))*J`.

The two residue premises have since been proved separately in the sibling
`compact44-low-mod-four-prototype`, but they remain explicit in **this**
theorem and this compile does not import that result. Identifying this rank
with a calibrated `CompactRankVariation.windowRank` for the same `c`,
selecting the auxiliary and outer Pell witnesses, and constructing the exact
free-J graph coordinates are further steps. This theorem does not prove a
positive graph zero, identify retained coefficient or PDF bytes, or prove
existence of an iPRA derivation.

The successful author-only run `observations/attempt04` rebuilt the exact
repository `ArithmeticRankForcing.lean` source before compiling this client,
in a fresh overlay over `/tmp/compact44-halt-rank-overlay-vp7w2rjg` and its
selected fallback roots. Both compiler processes actually exited 0; the
client reported precisely `propext`, `Classical.choice`, and `Quot.sound`
as Lean metatheory axioms, without warnings or `sorryAx`. These are not
additional axioms of the object theory. The generic and client object hashes
were `13724d5518f0d59a72d8874747804c1bed263f3d5e9a181e6023f4e3738e6b83`
and `8b464c1eaf47d305006000be52a124ed26ba3a6f8ab9bdc3984973baf205c13a`,
respectively. The client source SHA-256 is
`3b1b93098df93925072bee932f8fbc7fb66bdee6608c7c4cfedd923d059851e8`.
The terminal, direct import/companion guards and selected project inventory
are retained in the attempt directory. All pairwise overlapping names across
the four selected project-provider directories matched at preflight; their
counts and mismatch arrays are recorded in `overlap.json`. Direct import
guards and the selected project inventory were unchanged after successful
compilation. The runner did not continuously monitor memory or authenticate
the entire transitive, package or dynamic ancestry. This is one exploratory
author build, not a paired replay or independent artifact audit; hashes and
inventory checks are point-in-time observations.

Attempt 01 stopped at dependency scan because the fresh namespace shadowed
the provider, before any Lean compilation. Attempt 02 compiled the generic
module but failed on two local client elaboration errors; its exact client
and logs are retained. Attempt 03 compiled the generic module but hit the
200000-heartbeat limit while unfolding the concrete low mask; its exact source
and log are retained. Attempt 04 avoids that expansion by explicitly
unfolding the mask wrapper before applying the existing exact population
theorem. No source or build output from a failed client is used in the
successful argument.
