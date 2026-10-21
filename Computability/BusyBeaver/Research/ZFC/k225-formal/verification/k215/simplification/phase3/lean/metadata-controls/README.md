# Synthetic metadata controls

These controls test only the evidence reviewers. Their `/fixture` source paths, objects and typed-client records are invented; none is a compilation result. Two positive cases and sixteen rejection cases passed. [result.json](result.json) pins the tested sources and records each outcome.

To rerun into a new scratch directory: `python3 -B control.py --out /tmp/k215-phase3-metadata-controls-new`. This invokes no proof kernel. The final actual proof evidence is in the parent directory. Earlier control runs and the initial archive-policy revision remain in the original scratch history; they were not failed proof runs.
