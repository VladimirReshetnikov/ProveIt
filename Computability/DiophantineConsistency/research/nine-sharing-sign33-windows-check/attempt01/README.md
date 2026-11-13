# Windows diagnostic failed on unknown identifier

Author-observed outer session `50522` returned numeric exit 1. Retained state SHA-256 `accb8bc5fae815c4a739129b4dc6f9f3d4ee83b811033161fbdc6380e352ab6d`; pre-run producer survey `5e0a12ddb5419503ab2fc2418ee59db3d0185da0a11c2454870c3f17b34fc5f7`. The outer record is an author observation, not an independently observed transcript.

Lean exited 1 with no monitor stop. Its compile log SHA-256 `577ca38eca4bcad152d14f6927f7144a5a7e233c5d3e1d650ea1516f23a33d12` reports an unknown identifier `absdiff` in the theorem statement. The emitted axiom report includes `sorryAx` from the failed declaration and is not proof evidence; no successful object was recorded. Final candidate guard and post-success producer survey were not reached. Point-observation and inherited-provider limitations remain as in the parent README.
