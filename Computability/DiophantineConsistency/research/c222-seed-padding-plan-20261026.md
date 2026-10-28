# Bounded even self-labels for actual C222 seeds

26 October2026, root proposal. This is a new arithmetic checkpoint toward
the represented source-seed freshness obligation. It is not a proof of
raw CP/GIC, tagged Collection or actual source-axiom interpretation.

For internal bound B and arbitrary matrix code p, set

```
Q = wim (wim (B+1) (B+1)) p
c = ValidatorSeedImage222.pad Q.
```

Actual C222 self-implication gives Q↔p; double-negation introduction and
elimination give c↔p. Numeric constructor bounds give B<c, and the outer
implication tag gives c%2=0. Therefore a,b≤B imply the exact seed gates
c≠a,b. Apply actual seed_pair a b c c and its literal request/closure
congruences to replace only the matrix c by p while retaining binder c.
This gives an actual proof of ex c (imageBody a b c p).

If F,Bstack≤B, constructor index bounds also give FreeAvoid c F and
Avoid c Bstack. Fallback1 is excluded by pad Q>3, including bound0.
If s%2=1, congruence modulo2 proves StreamAvoid c s for
the whole future binder stream. For a typed source matrix p encoded at
F,Bstack,s, the accepted encode_vac theorem then supplies actual Vac c
(encode F Bstack s p) under its explicit IΣ2 and stack-length premises.
Thus self-code freshness can be proved by bounded padding and parity;
no source-occurrence compiler is needed for this particular checkpoint.

Proposed files: ValidatorSeedPadding222.lean and Checks, importing only
ValidatorSeedImage222 and ValidatorEnvironmentStreams222. Both are actual
C222 resources. Read root SeedImage main and its complete accepted receipt,
the numeric constructor bounds, actual StreamFree/StreamAvoid definitions,
and encode_vac contracts. The exact reachable union is160 cached modules,
117 Foundation modules,511 artifacts and40 existing external boundaries.
All shared sources/objects of the accepted derivation planning inventory
and SeedImage inventory agree. Select the independent SeedImage root
primary; no prerequisite or Foundation build is needed.

The intended two fresh private leaves use Lean4.32 -M6000 -j1
-DElab.async=false, one thread and512MiB reserve checks. Fully read every
source/check/driver before execution and preserve all failed attempts.
Checks retain arbitrary internal bounds, arbitrary matrices including0,
coincident a=b, literal seed freshness, even/odd stream separation and
actual History222 witnesses. No source-theory premise is discharged here.
