#!/usr/bin/env bash
set -euo pipefail
: "${PA194_STARTUP_OVERLAY:?Set PA194_STARTUP_OVERLAY to the audited parent-startup object directory}"
repo=${PA194_REPO:-$(git -C "$(dirname "$0")" rev-parse --show-toplevel)}
cd "$repo"
PA194_STARTUP_OVERLAY=$(realpath "$PA194_STARTUP_OVERLAY")
base=Computability/BusyBeaver/Research/PA
code=$base/pa194/ipra/machine-code
if [ "${PA194_DENSE_CHECK_BLOCKS:-46}" = 46 ]; then
  : "${IPRA_MODEL_OVERLAY:?Set IPRA_MODEL_OVERLAY to the audited PA194 model object directory}"
  : "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
  IPRA_MODEL_OVERLAY=$(realpath "$IPRA_MODEL_OVERLAY")
  IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
  sha256sum -c <<PINS
22bed0bb4056e6cd907e7eff1b41d8f04969b322882e9ed07d3fb6c78f34ec75  $IPRA_MODEL_OVERLAY/PA194StepperZip.olean
ce25e4ed24fb5dcd1fbc092b92badb9414d55e61c9322a8cda443bf0e16d6989  $IPRA_MODEL_OVERLAY/ConfigurationStandard.olean
b9269d801d460aec8798c804f69a05088135b5798c27140f58dd2c4967076df6  $IPRA_MODEL_OVERLAY/PA194Bounded.olean
136ae4b2be8d8ad0b4787f954547e7602934eb2578f87c8c0b57640cfe950c7a  $IPRA_MODEL_OVERLAY/DiophantineConsistency/PRAMultiplication.olean
d41eeef2c3e75cfa8687884577528cb329e700772266ff48c75d99cb13e9b1fc  $IPRA_MODEL_OVERLAY/PA194FiniteControls.olean
7188c01a8a69007f6963186593c316729e9773651004fe010f6cea5650795160  $IPRA_MODEL_OVERLAY/PA194StateOne.olean
c67826dc3cb54643f65e707efa932eba92b443f704348ed8bb2f509dd2f938f6  $IPRA_MODEL_OVERLAY/PRAEqualityToIPRA.olean
PINS
  model_path="$IPRA_MODEL_OVERLAY:$IPRA_FOUNDATION_OVERLAY:"
else
  model_path=''
fi
sha256sum -c <<PINS
152d1d552b27baca8db0ac05b16092d9083c2ab979bb0b4e7f96a95803d9a9b0  $base/other-machines/jamesyc-upstream/pa196/M6/Zip.lean
bfb3245b742173c47f94222800fdccb189f26486140bc69db844f7e9870e1deb  $base/other-machines/jamesyc-upstream/pa196/PA196/FastRun.lean
1c6476ea202824eeea7d690d7e5e544f6026adf4e5386152d03097aeed6ed0c5  $base/pa194/ipra/generate.py
6ff179c3180b5ff2597a03048eaf0659285180d2dcf85c7629393bb48b236960  $base/pa194-work/pa194-startup/generate.py
d57c38ab650fd64a527960e9868645a4f5f03616fefd41d5cc207e77d15ced8e  $PA194_STARTUP_OVERLAY/PA194PrimitiveSimulation.olean
382135ae061e88ad738564f356f012a3acded7065d55c18601b42f9293bb702f  $PA194_STARTUP_OVERLAY/PA194SourceProgram.olean
PINS
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-dense-startup.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6" "$task_dir/PA196"
# Lean resolves a module namespace at its first matching search root. Link the
# retained parent prerequisites there, then rebuild the two pinned modules.
cp -as "$PA194_STARTUP_OVERLAY/M6/." "$task_dir/M6/"
cp -as "$PA194_STARTUP_OVERLAY/PA196/." "$task_dir/PA196/"
rm -f "$task_dir/M6/Zip.olean" "$task_dir/M6/Zip.olean.private" \
      "$task_dir/M6/Zip.olean.server" "$task_dir/M6/Zip.ir" \
      "$task_dir/PA196/FastRun.olean" "$task_dir/PA196/FastRun.olean.private" \
      "$task_dir/PA196/FastRun.olean.server" "$task_dir/PA196/FastRun.ir"
python3 "$base/pa194/ipra/generate.py" "$repo" "$task_dir"
python3 "$base/pa194-work/pa194-startup/generate.py" --out "$task_dir" --start-block 0 --stop-block 1
printf '%s  %s\n' 7cd4f1ae6f6f5d0ee476840d6e7aa447500a3ec4e2293f6830e672cca735bbd7 "$task_dir/PA194StartupData.lean" | sha256sum -c
python3 "${PA194_DENSE_GENERATOR:-$code/generate-dense-startup.py}" "$repo" "$task_dir"
export LEAN_PATH="$task_dir:$model_path$PA194_STARTUP_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/M6/Zip.olean" "$base/other-machines/jamesyc-upstream/pa196/M6/Zip.lean"
lean -M6000 -j1 -R "$task_dir" -o "$task_dir/PA194Literal.olean" "$task_dir/PA194Literal.lean"
lean -M6000 -j1 -o "$task_dir/PA196/FastRun.olean" "$base/other-machines/jamesyc-upstream/pa196/PA196/FastRun.lean"
lean -M6000 -j1 -R "$task_dir" -o "$task_dir/PA194StartupData.olean" "$task_dir/PA194StartupData.lean"
lean -M6000 -j1 -R "$task_dir" -o "$task_dir/PA194DenseStartupData.olean" "$task_dir/PA194DenseStartupData.lean" | tee "$task_dir/data-axioms.log"
if rg -q 'sorryAx' "$task_dir/data-axioms.log"; then
  echo 'Unexpected sorryAx in startup data' >&2
  exit 1
fi
python3 - "$task_dir" "${PA194_DENSE_JOBS:-2}" "${PA194_DENSE_CHECK_BLOCKS:-46}" <<'PY'
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import subprocess
import sys
root = Path(sys.argv[1])
jobs = int(sys.argv[2])
count = int(sys.argv[3])
if jobs < 1:
    raise SystemExit('PA194_DENSE_JOBS must be positive')
modules = sorted(root.glob('PA194DenseStartupBlock*.lean'))
if len(modules) != 46:
    raise SystemExit('unexpected dense startup block count')
if not 1 <= count <= 46:
    raise SystemExit('PA194_DENSE_CHECK_BLOCKS must be between 1 and 46')
modules = modules[:count]
def check(path):
    log = path.with_suffix('.log')
    with log.open('w') as out:
        p = subprocess.run(['lean', '-M6000', '-j1', '-R', str(root), '-o',
                            str(path.with_suffix('.olean')), str(path)],
                           stdout=out, stderr=subprocess.STDOUT)
    return path, p.returncode, log.read_text()
failed = []
with ThreadPoolExecutor(max_workers=jobs) as pool:
    for future in as_completed([pool.submit(check, p) for p in modules]):
        path, rc, output = future.result()
        print(path.name, 'passed' if not rc and 'sorryAx' not in output else 'FAILED', flush=True)
        if rc or 'sorryAx' in output:
            print(output, file=sys.stderr)
            failed.append(path.name)
if failed:
    raise SystemExit('failed startup batches: ' + ', '.join(failed))
PY
if [ "${PA194_DENSE_CHECK_BLOCKS:-46}" != 46 ]; then
  echo 'Partial replay only; the complete startup theorem was not checked.'
  exit 0
fi
lean -M6000 -j1 -R "$task_dir" -o "$task_dir/PA194DenseStartupComplete.olean" "$task_dir/PA194DenseStartupComplete.lean" | tee "$task_dir/final-axioms.log"
if rg -q 'sorryAx' "$task_dir/final-axioms.log"; then
  echo 'Unexpected sorryAx in literal startup theorem' >&2
  exit 1
fi

# Rebuild the bridge from ordinary literal runs to the internal model stepper.
# The remaining imported objects come from the pinned audited model overlay.
model_source=${PA194_MODEL_SOURCE_DIR:-$code}
for module in PA194StandardCodeBridge PA194StandardStepperBridge PA194PackedNumeralBridge PA194ModelDenseStartup PA194StartupSentence; do
  lean -M6000 -j1 -R "$model_source" -o "$task_dir/$module.olean" "$model_source/$module.lean" | tee "$task_dir/$module.log"
  if rg -q 'sorryAx' "$task_dir/$module.log"; then
    echo "Unexpected sorryAx in $module" >&2
    exit 1
  fi
done
