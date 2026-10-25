# Correction to ROOT's first full kernel49 ordinary review

The frozen first ROOT review contains a false sentence: “All six
factors become1”. It conflates the normalized strong-norm factor with
the actual printed, unscaled Ns. The first report pair remains byte
identical in commit27c7d6bee3 and is not silently repaired. The source
kernel proposal does not make that false assertion and is unchanged.
No acceptance follows from its original unqualified PASS alone.

This outside correction replaces that ONE review statement by the
following exact whole-equation calculation. With the freshly constructed
strong Pell data, the printed definitions give

    f^2=1+Delta*i^2*c^4, S=i*Delta*c^2,
    S^2=Delta*(f^2-1), Ns=Delta*f^2-S^2=Delta.

The five other ACTUAL factors are

    N0=N1=Na=Nk=Nt=1.

Consequently their product with Ns is Delta, and the printed equation
N0*N1*Na*Nk*Nt*Ns-Delta=0 holds. Claiming six actual factors1
would instead give1-Delta and would be wrong because Delta>1 here.

For soundness the exact normalization, used only in the PROOF, is

    ns=Ns/Delta=f^2-Delta*i^2*c^4,
    P66=Delta*(N0*N1*Na*Nk*Nt*ns-1).

Since Delta>0, the normalized integer product is1. The retained sign
and Pell recovery applies to these six integer units, with the printed
Ns restored as Delta*ns. No arbitrary witness division or polynomial
change is made. The first review's whole native/rank/controller and
both fresh positive witness maps remain valid with this explicit final
calculation; all other first review statements have been reread and no
additional finding has been identified.

ROOT freshly read the complete476-line source and233-line pins, the
entire first MD and substantive JSON, and now reauthenticates ALL28
direct records, all own members, all three complete49/51/53 parents
and protected main files against the first snapshot. Earlier whole
primitive/Pell/source reads are reused only after exact authentication.
The initial kernel lead was supplied by ROOT, as disclosed in the
first report; this is no independent-discovery claim. The independent
FULL peer report and separate ROOT conditional acceptance are still
required. This correction confers no runtime authority, finite lambda
result, endpoint, shorter page or Lean theorem.

The error was noticed when the independent low-bit-padding reviewer
caught the same all-one wording in ROOT's separate frozen author note.
That note is separately blocked as written. Neither its source nor its
review is relabeled as accepted by this kernel-review correction.
Only generic inert text/JSON/hash/member readers and this outside
report writer ran. No candidate, math helper, import, AST, compiler,
coefficient/residue/prime/Pell evaluation, Lean, TeX or PDF process ran;
no source, probe, parent or maintained page was changed.
