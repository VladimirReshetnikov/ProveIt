# Sign27 first cut: failed author-observed run

The author observed outer session 24677 exit 1. Dependencies succeeded, but Lean compilation exited 1: the N1-zero proof left `ι (v 21) * 2 - ι (v 21) * ι 2 = 0` unsolved. The log also reports one unused-simp warning. The printed N1-zero report contains `sorryAx`; no declaration from this failed module is credited, and final postflight did not run.

The retained state SHA-256 is `0d3d8fd1f314a2eb6153c3bc166d6dd434d40b4098717b19a95e579cb20a601e`; author outer receipt SHA-256 is `bb9e4d910aa2450b38af114bba531f05bf6bb4bf0254f07c6ff4f7cd2373306f`. The numeric outer exit is author-observed rather than independently replayed. Historical plan README-link and deeper ancestry caveats remain inherited.
