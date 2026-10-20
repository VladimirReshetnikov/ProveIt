# Selected StateSearch219 replay

Choose fresh directories outside the repository. After recovering the archive
in its original wrapper layout, run the portable reviewer adapters:

```sh
python3 -B prepare.py --packet /tmp/intake189-recovered/ZFC_218_State_Search_2026-10-20/ZFC_218_State_Search_2026-10-20 --output /tmp/stateseach219-direct
python3 -B run.py --work /tmp/stateseach219-direct
```

Here `prepare.py`, `run.py` and `direct.py` are the portable adapters from this
review. Preparation safely reads the pinned nested ZIPs and recovers exactly
the baseline machine data and five runtime dependencies. It does not execute
an archive wrapper or predecessor verification suite. It writes a concrete
five-job plan. The serial runner invokes the unchanged independent rho6
closed-subtree check and the reviewed source, startup and runtime functions
through `direct.py`, without invoking the original `replay.main` or its
manifest loop.

The original scratch execution used `actual-adapter/prepare.py` to copy those
same already recovered inputs from intake188. The portable successor instead
recovers them directly from this packet's vendor ZIP; its selected plan was
tested to equal the executed plan after work-path normalization. The exact
preparation/run diffs are retained. Heavy runtime checks were run once.

Three small jobs have 60-second process caps; each full runtime has 240 seconds.
Assertions remain enabled. A failure or timeout retains logs and stops the
serial run. The final own status is `FRESH_DIRECT_LEAVES_PASS`, not the
delivered wrapper's full-replay label. Outputs include exact binding/source
and complete sparse/dense blank-startup records, fresh ordered runtime cases,
their byte comparison with delivered cases, and raw stdout/stderr.

Both verified variants still have 219 working states. This selected replay
does not rerun other research searches, theory scripts, checksum/manifest
suites, ancestor suites, or Rocq/Coq/Lean. The runtime driver does not expose
all-row-use coverage, so no such claim is added.
