# K215 bounded well-formedness assembly guard

This isolated 18-stage client rebuilds identical table data, all sixteen bounded node checks, and the full `wfCheck222` assembly from the authenticated fresh base. It preserves the original project source. The assembly is a proposed proof until its own Lean run passes, and compatibility with the original module requires a separate guarded proof. Existing package and dynamic ancestry limitations remain.

Caps remain: Lean `-M3600 -j1`, 4 GiB sampled child RSS, 180 seconds per child, 10 GiB host available memory, and a 5.1 GB sampled disk stop. The six-hour budget triggers a stop; forced receipt and cleanup, including log hashing, may finish later. Existing outputs are never removed.

`python3 -I -S -B controls.py` and `run.py --preflight` do not launch Lean. Only `run.py --run` starts the guarded build, subject to independent prelaunch and slot allocation.

Attempt01 passed: outer session 5878 exited 0, all 18 stages and postflight passed. The [independent terminal audit](../../reviews/current14-k215-wf-assembly-terminal-independent/) checked the proof reports and producer routes. This establishes the helper-table `wfCheck222`; its use in the original module and a coherent endpoint rebuild remain separate.
