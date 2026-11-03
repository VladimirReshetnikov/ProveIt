# Outer seed and transport equations imply both graph carriers

`carrier_units` proves that both actual 95-operation free-J carrier factors
represent `+1` in any `IΣ₁` model, using the same graph valuation throughout.
It combines the model `SeedRelations` with these explicit assumptions:

- Graph coordinates 5, 6, 8 and 9 equal `X=2^R`, `Y=s·(2^u)^3`, `η`, and `ζ`.
- `X=q·w` and `U·γ+U·w=U·γ_old+(k−R−1)` hold in the model's difference ring,
  with `γ` the graph coordinate and `γ_old` the seed's model-natural `gamma`.
- The additive first-carrier transport equation from
  [the graph transport bridge](../free-j-first-transport-identity-prototype/README.md)
  holds for the seed's `τ` and the same graph expressions.

The theorem uses the exact checked `Z=Mτ` and `Dstar=Uχ` identities and maps
the actual model seed squares into the difference ring. It does not construct
the graph valuation, establish the additive or linear equations or positivity,
prove the third factor, calibrate fixed ports, or produce an iPRA proof.

Bounded single-author attempt 02 exited 0 in 5.081 seconds without warnings or
`sorryAx`. Source SHA-256 was
`199e8674f7182ce263bb7a857b721d304a11ec8313de9292c1445d279df70b6f`;
object `/tmp/free-j-outer-seed-transport-join-author-uydqgos6/FreeJOuterSeedTransportJoin.olean`
had SHA-256
`9b4a723613e6e0ec386ffd6c1d1d41a720e60da63b2957f309bb7cb6e37d9a8c`.
All three provider overlaps were checked byte-for-byte; 1,181 live provider
files and direct/named transitive bridge object companions remained unchanged.
This does not independently replay provider ancestry or audit dynamic and
package-transitive dependencies. Lean reports `propext`, `Classical.choice`,
and `Quot.sound` as metatheoretic dependencies.

Attempt 01 elaborated but the runner rejected a style warning. Its source and
log are retained; attempt 02 removed the warning without weakening the theorem.
