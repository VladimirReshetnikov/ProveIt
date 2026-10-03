#!/bin/sh
# Full verification against the exact published source bytes, with fresh outputs.
set -eu
cd "$(dirname "$0")"
ROOT=$(pwd)
if [ -n "${PYTHONOPTIMIZE:-}" ]; then
  echo 'Unset PYTHONOPTIMIZE: the full suites require assertions.' >&2
  exit 1
fi
PYTHON=${PYTHON:-python3}
"$PYTHON" -c 'import sys; assert sys.version_info >= (3,10), "Python 3.10+ required"; assert __debug__'
OUT=${1:-"$ROOT/.replay/run-$(date -u +%Y%m%dT%H%M%SZ)-$$"}
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
mkdir -p "$OUT/producer" "$OUT/independent" "$OUT/clock" "$OUT/clock-optimized" "$OUT/examples"
printf 'Replay output: %s\n' "$OUT"
export PYTHONDONTWRITEBYTECODE=1

echo 'Checking the native collision generator and inverse'
"$PYTHON" code/three_mass_collision_generator.py > "$OUT/generator-tests.json"
"$PYTHON" code/test_three_mass_independent.py > "$OUT/independent-ca-tests.json"
"$PYTHON" code/test_size_ledger.py --generator code/three_mass_collision_generator.py > "$OUT/size-ledger-tests.json"
echo 'Checking certificate semantics and actual native/radius-one trajectories'
"$PYTHON" code/test_certificates.py --generator code/three_mass_collision_generator.py \
  --radius-one code/radius_one.py --output-dir "$OUT/producer" \
  --receipt "$OUT/certificate-tests.json" > "$OUT/producer.log"
"$PYTHON" code/test_certificates_independent.py --source-dir code \
  --output-dir "$OUT/independent" > "$OUT/independent.log"
"$PYTHON" code/test_checker_mutations.py --source-dir code \
  --output-dir "$OUT/independent" > "$OUT/checker.log"
"$PYTHON" code/test_certificate_hardening.py --source-dir code \
  --output-dir "$OUT/independent" > "$OUT/hardening.log"
echo 'Checking radius-one full-shift behavior and strict API boundaries'
"$PYTHON" code/test_radius_one.py --generator code/three_mass_collision_generator.py \
  --output "$OUT/radius-one-tests.json" > "$OUT/radius-one.log"
"$PYTHON" code/test_radius_one_boundaries.py > "$OUT/radius-boundaries.log" 2>&1
"$PYTHON" -O code/test_radius_one_boundaries.py > "$OUT/radius-boundaries-optimized.log" 2>&1
"$PYTHON" code/test_spatial_radius_one.py --output "$OUT/spatial-radius-one-tests.json" > "$OUT/spatial-radius-one.log"
"$PYTHON" -O code/test_spatial_radius_one.py --output "$OUT/spatial-radius-one-optimized-tests.json" > "$OUT/spatial-radius-one-optimized.log"
echo 'Checking exact clock scaling and pre-clock serialized compatibility'
"$PYTHON" code/test_clock_scale_independent.py --source-dir code --legacy-dir code/legacy \
  --output-dir "$OUT/clock" > "$OUT/clock.log"
"$PYTHON" -O code/test_clock_scale_independent.py --source-dir code --legacy-dir code/legacy \
  --output-dir "$OUT/clock-optimized" > "$OUT/clock-optimized.log"
echo 'Checking two-mass encounter/observation arithmetic and literal rule bytes'
"$PYTHON" code/test_two_mass_arithmetic.py > "$OUT/two-mass-arithmetic-tests.json"
"$PYTHON" code/test_literal_exports.py > "$OUT/literal-export-check.json"
"$PYTHON" code/export_examples.py "$OUT/examples" > "$OUT/literal-export.json"
for name in chain mixed mixed_radius_one; do
  cp "examples/${name}_request.json" "$OUT/examples/${name}_request.json"
  "$PYTHON" code/certificate.py export "examples/${name}_request.json" \
    "$OUT/examples/${name}_certificate.json" --expanded
  "$PYTHON" code/certificate.py witness "$OUT/examples/${name}_certificate.json" \
    "$OUT/examples/${name}_witness.json"
  "$PYTHON" code/checker.py "$OUT/examples/${name}_certificate.json" \
    "$OUT/examples/${name}_witness.json" --receipt "$OUT/examples/${name}_check.json" > /dev/null
done
"$PYTHON" - "$OUT" <<'PY'
import hashlib, json, sys
from pathlib import Path
out=Path(sys.argv[1]); root=Path.cwd()
checks=[]
for p in sorted((root/'examples').glob('*.json')):
    fresh=out/'examples'/p.name
    if not fresh.is_file() or p.read_bytes()!=fresh.read_bytes():
        raise SystemExit('Example byte mismatch: '+p.name)
    checks.append(p.name)
for p in out.rglob('*.json'):
    value=json.loads(p.read_text())
    if isinstance(value,dict) and 'status' in value:
        if value['status'] not in ('PASS','passed'):
            raise SystemExit('Non-passing receipt: '+str(p))
report={'status':'PASS','example_files_byte_identical':len(checks),
        'examples':checks,'source_sha256':{
            p.relative_to(root).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted((root/'code').rglob('*.py'))}}
(out/'replay-summary.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: all replay suites; '+str(len(checks))+' example files byte-identical')
PY
printf 'Fresh summary: %s/replay-summary.json\n' "$OUT"
