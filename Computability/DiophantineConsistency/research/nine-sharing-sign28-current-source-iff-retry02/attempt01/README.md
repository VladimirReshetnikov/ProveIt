# Explicit-transitivity retry: failed author-observed run

Outer session 24903 exited 1. Dependency checking exited 0; Lean compilation exited -6 with an uncaught `lean::memory_exception` at `interpreter`. The monitor recorded no stop reason or errors and sampled peak session RSS of 2,939,375,616 bytes. The exact trigger is unknown. No theorem from this failed stage is counted, and final postflight did not run. The earlier imports-only success does not imply a diagnosis.

The retained state SHA-256 is `f3c8869fe73c5ca2f6acf262c8c856c2b3ca74124372549abff406c2d7c6bd0e`; author outer receipt SHA-256 is `aad820136968dab5b6445faa5e3715a59778d9c6423d31d32dd5b6fc3c392785`. The numeric outer exit is author-observed rather than independently replayed; sampling can miss transient spikes or escaped descendants.
