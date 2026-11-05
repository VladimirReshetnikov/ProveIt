#!/usr/bin/env python3
"""Read-only hash and synthetic receipt cross-check; no driver or Lean execution."""
import hashlib,json,sys
from pathlib import Path
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise SystemExit('requires python3 -I -S without -O')
root=Path(__file__).resolve().parents[2]
p=root/'research/current14-printed-port-extension-coordinator'
pins={'coordinator.py':'f898dad6a47934e698249d25545964b7b4dd657a3f4275f0a45c49a1cdce480b',
'verify.py':'005b0f48f6cb83a3d62c4aa5e5cf5ee3d7cd651e674916f114832b68071061ac',
'controls.py':'10bba53b815076880c50b3f73172f222906f826e67d541f569393cf826a4d93d',
'controls-observation.json':'788234816498e3e07dda3a121b2869cafe5ac5ea2781f9eb153df7937e96762c'}
for name,digest in pins.items():
    if hashlib.sha256((p/name).read_bytes()).hexdigest()!=digest:raise RuntimeError('hash mismatch: '+name)
r=json.loads((p/'controls-observation.json').read_text())
if r['status']!='PASS' or r['coordinator_sha256']!=pins['coordinator.py'] or r['verify_sha256']!=pins['verify.py']:raise RuntimeError('receipt mismatch')
keys={'actual_running_base_refused','external_namespace_shadow_rejected','missing_row_rejected','monitor_failure_waits_for_child','mutated_output_rejected','mutated_source_rejected','nonzero_outer_exit_rejected','optimized_python_refused','synthetic_61_row_terminal_accepted','terminal_pin_mismatch_rejected','unexpected_companion_rejected','unexpected_import_rejected','unexpected_overlay_file_rejected'}
if set(r['controls'])!=keys or r['controls']['synthetic_61_row_terminal_accepted']!=61 or r['controls']['monitor_failure_waits_for_child'] is not True:raise RuntimeError('controls mismatch')
print(json.dumps({'status':'PASS','controls_count':len(keys),'source_pins':pins,'scope':'Static hash and retained synthetic receipt cross-check only; no coordinator, tests, or Lean launched.'},sort_keys=True))
