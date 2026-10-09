# Incoming normal-ray-block test compatibility

Only `tests/test_normal_ray_blocks.py` was adapted; native production code is unchanged.
The current native `normal_disk_kernel.normal_compressing_disk_count` defaults to
`unit_ray=True`. After canonical vertex-link peeling and scalar reduction, the
mixed five-tetrahedron test vector has a primitive meridional unit-ray core.
The native producer therefore emits `normal-disc-count-v2` with zero orbit cycles,
even though the outer support-block engine classifies the mixed support as a
fallback block. The previous positive-cycle assertion targeted the older schedule.

The adapted test first checks the native optimized answer at a zero cycle cap,
with orbit discovery patched to raise, and independently verifies its v2 proof.
It then patches only the outer engine's imported call with the same native
producer using its supported `unit_ray=False` option. This explicitly selects the
legacy v1 component-census schedule and retains the original positive-cycle,
under-budget inconclusive, exact-budget complete, and independent-replay checks.
No assertion was weakened to ignore fallback work.

Validation: `python -m unittest tests.test_normal_ray_blocks -v` passed all 14 tests.
The native kernel SHA-256 before and after was
`cfee4f5245230b1efd64a5cb3330b0b3fa3bb5d7ef6f65f49b9319cdb56ebb0b`.
The exact compatibility diff is `normal_ray_blocks_compatibility.patch`.
