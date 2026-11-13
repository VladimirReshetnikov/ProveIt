# Direct sign28 endpoint: failed author-observed run

The author observed outer session 57672 exit 1. Native-stage dependency checking exited 0, but Lean compilation exited -6 with an uncaught `lean::memory_exception` at `interpreter`. The monitor recorded no stop reason or errors and sampled peak session RSS of 2,937,425,920 bytes. The exact trigger is unknown. No native theorem is credited; standard and translated stages and final postflight did not run.

Retained state SHA-256 is `406bf7eee5ee07ccb6c652f7a4f4736950a7f43408b2e21a031ac62288f177ab`; author outer receipt SHA-256 is `61e88f46f35895f7bfc19f2c7db3267edae886e9a82ba810d3c84566cbaa0b0b`. The outer exit is author-observed, not independently replayed; sampling may miss transient spikes or escaped descendants.
