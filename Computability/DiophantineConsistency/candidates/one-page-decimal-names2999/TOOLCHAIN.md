# Held seed conversion only: three independent ROOT commands

NOT RUN. Two complete nonauthor statics and a distinct ROOT release are required.
This author file grants no execution authority. No TeX or PDF command is included.

After release, ROOT reauthenticates HOLD, every source/input and both physical
executables plus the python3 symlink. The installed Python standard library,
ordinary shell and OS are explicitly trusted; no transitive runtime pin is claimed.
Require BOTH fixed trees absent, INCLUDING symlinks:

    /tmp/decimal-names2999-materialized-v1
    /tmp/decimal-names2999-captures-v1

ROOT creates only the capture tree, once. The converter exclusively creates its
own separate output tree. Working directory for every command is the repo root.
Before each process require its streams and receipt absent. Retain exact commands
and tool-observed actual exits with exclusive inert 01.exit/02.exit/03.exit writers
after each process; no shell wrapper substitutes an inferred exit status.
Stop dependent commands at the FIRST nonzero exit; retain every byte and do not
retry, remove outputs or repair source. The immutable source and parents stay exact.

1. Sole materialization, after inert preflight; all data gates/controls run first:

```sh
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C TZ=UTC \
  /usr/bin/python3 -I -B -S Computability/DiophantineConsistency/candidates/one-page-decimal-names2999/seed_to_decimal.py --write \
  > /tmp/decimal-names2999-captures-v1/01.stdout 2> /tmp/decimal-names2999-captures-v1/01.stderr
```

2. Only after actual exit0; readonly whole-output/roundtrip/control verification:

```sh
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C TZ=UTC \
  /usr/bin/python3 -I -B -S Computability/DiophantineConsistency/candidates/one-page-decimal-names2999/seed_to_decimal.py \
  > /tmp/decimal-names2999-captures-v1/02.stdout 2> /tmp/decimal-names2999-captures-v1/02.stderr
```

3. Only after actual exit0; same readonly checks with optimization enabled:

```sh
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C TZ=UTC \
  /usr/bin/python3 -I -B -S -O Computability/DiophantineConsistency/candidates/one-page-decimal-names2999/seed_to_decimal.py \
  > /tmp/decimal-names2999-captures-v1/03.stdout 2> /tmp/decimal-names2999-captures-v1/03.stderr
```

The output tree must contain exactly two regular nonsymlink files: decimal.txt
and RECEIPT.json. Both readonly runs compare their ENTIRE bytes to the freshly
derived deterministic payloads. stdout also records written/optimized flags;
the saved data excludes those mode flags and must remain identical in all modes.
The capture tree retains all six streams and three actual command/exit records.
No Python --version, project import, general parser, coefficient materializer,
port decompression, mathematical evaluator beyond this bounded conversion, Lean,
TeX, PDF utility or image tool is authorized. A later exact literal TeX source
review and DISTINCT typesetting release are needed before any new page rendering.
