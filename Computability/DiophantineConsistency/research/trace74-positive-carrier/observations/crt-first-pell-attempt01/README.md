# Failed first CRT/first-Pell join check

Lean 4.32.0 session 80150 exited 1 on the retained source. The final
`simpa only [ports,map_natCast] using hdiv` left the port function cast
incompatible; the theorem axiom print therefore included `sorryAx`. The
preceding CRT application and coordinate-1/2 preservation proof steps
elaborated, but this attempt is not an accepted proof. The next version adds
an explicit function equality between `ι (p j : V)` and `ports p`.
