# Separate ROOT release of the first two fixed modular-probe commands

ROOT now releases ONLY commands1 and2 in the unchanged held TOOLCHAIN:
the first normal and first optimized execution of the fixed standalone
radix65 modular probe. Both complete final static approvals are preserved
in698169876c and842b447d5a. ROOT read the full independent review and all
its substantive JSON checks; both verdicts are PASS with no finding.
This release is a distinct execution decision after those approvals.

The only approved source is `research/compact66-radix65-unit-probe`,
HOLD SHA256
`95a35b886d4eb1f4d43afef74b2de299c619f1612d721b1e36d18e9664f475d8`
and SOURCE_PINS
`7d63f4fa104e06afd6dd2ba65f0e6ace041fecd4027e9926af130923010afa81`.
All six held files and115 direct inputs remain identical to the121-file
ROOT pre-execution snapshot. Its path is
`/tmp/compact66-radix65-unit-probe-root-pre-execution-snapshot.json`.
The independent reviewer also authenticated all three whole parent sets.
All twelve planned receipt/capture paths were absent in both full statics;
ROOT must recheck the six first paths immediately before launch.

Run sequentially from `Computability/DiophantineConsistency`:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 research/compact66-radix65-unit-probe/probe.py --output /tmp/compact66-radix65-unit-probe-normal.json > /tmp/compact66-radix65-unit-probe-normal.stdout 2> /tmp/compact66-radix65-unit-probe-normal.stderr
```

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -O research/compact66-radix65-unit-probe/probe.py --output /tmp/compact66-radix65-unit-probe-optimized.json > /tmp/compact66-radix65-unit-probe-optimized.stdout 2> /tmp/compact66-radix65-unit-probe-optimized.stderr
```

Observe each actual process exit before the next command. Stop at the
first application failure, preserve complete streams and available data,
and do not repair, retry, overwrite, change paths or run another variant.
A successful first command also requires complete JSON==stdout, empty
stderr, PASS, all seven negative/two valid controls and the whole source
binding before proceeding. Compare complete normal/optimized reports after
removing only optimized_python. Recheck all121 source inputs afterwards.

A verified zero unknown residue is a legitimate PASS scientific outcome,
not an application failure or a reason to change this release. No unknown
value or nonvanishing is assumed here. The only previously expected H0
residue remains4 modulo5. The new65-bit evaluation is modular only; this
release constructs no new tuple/masks, native word, calibrated endpoint,
polynomial, TeX/PDF or Lean result, and invokes no adopted application.

Commands3/4, any other application/helper/import/compile, repair, search,
native/source/calibration replay or maintained-page change remain outside
this release. ROOT must separately release fresh reproduction after
preserving and examining both complete first outcomes. Subsequent inert
outside result/provenance recording is permitted; the held directory must
stay exactly six files. The accepted67-bit tuple and compact66 page remain
current, Lean paused and reduction research active.
