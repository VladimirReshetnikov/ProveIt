# Sign28 current-source iff: failed author-observed run

The actual outer session 16022 exited 1 after the compile stage failed. The dependency stage exited 0; Lean compile exited -6 and its log reports an uncaught `lean::memory_exception` at `interpreter`. The monitor recorded no stop reason, a sampled peak session RSS of 2,939,822,080 bytes, and no monitor errors. The exact trigger of the exception is unknown. No declaration from the failed compile is counted as proved, and final postflight did not run.

The retained state SHA-256 is `f63796abaa97d61d9125b8929cbeb0056e0e3db117487eb17f6a755d2ff78565`; the author outer receipt SHA-256 is `80cd40737380376576a28f6bb37fd17b1c91e0b286c049e0c942c01e4d319278`. The outer exit is author-observed rather than independently replayed. The sampled monitor can miss transient spikes or escaped descendants.
