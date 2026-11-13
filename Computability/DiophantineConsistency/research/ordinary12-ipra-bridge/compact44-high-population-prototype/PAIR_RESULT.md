# Paired symbolic high-mask population replay

The previously exploratory `model_population` and `model_lt` declarations
now have matching author and peer builds. With the source snapshot held at
commit `489e687891`, the clean-loader replay actually exited 0 in outer
session 45763; both Lean children exited 0, produced matching objects and
reports, and the endpoint-successor parent audit matched before and after.
The receipt SHA-256 is
`fff835ad2b2f579da55100d9c93344a2f43732d6b5c5409221f47c990df4e03b`.
This result supersedes the original README's historical statement that the
paired replay had not yet run; that README is an exact prelaunch-audit input.

These declarations prove population 986 and the word bound for the cast
symbolic high digit-list value in every `IΣ₁` model. Their scope remains as
stated in the pinned original README: the retained shifted MF/β comparison is
external, the graph-port equality and mod-8 residue are not proved, and no
machine simulation or iPRA endpoint follows. Both reports list Lean metatheory
`propext`, `Classical.choice`, and `Quot.sound`; neither log contains warnings
or `sorryAx`. Independent artifact review of this pair remains outstanding.
The endpoint provider's outer-wrapper, package-transitive and dynamic ancestry
qualifications remain; memory reports are samples.
