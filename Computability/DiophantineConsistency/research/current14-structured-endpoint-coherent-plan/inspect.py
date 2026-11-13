#!/usr/bin/env python3
"""Read-only source-interface and current readiness observation; no Lean."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent
TASK=HERE.parents[1]
PINS={
    'research/current14-literal-port-assembly/Current14LiteralPorts.lean':'b19dfc3f5ea1639dcd6003613cd587992d3ab64f707cbe7c9fb61a466092f8b0',
    'research/current14-structured-endpoint-draft/StructuredEndpoint.lean':'31b2869c63f33610beac36cec7bcbcbcbfc00579b106fbc130ce0f754702a392',
    'research/current14-printed-port-extension-driver/driver.py':'97fabce00462b878ce9c91fd60ffbc54030350b06e564a0578a62dc5550971e1',
    'research/current14-printed-port-extension-driver/guards.py':'e42ef7c73da49653b1d664b947c3a9ea5fa2ae78206d0988472a948a901fafc3',
    'research/current14-printed-port-extension-plan/result.json':'cb1817489d0ea7ca5cb3f805acd857a7e22e68659fc664e03b8360d70f4f231c',
    'research/current14-standard-fresh-rebuild-preflight/snapshot-manifest.json':'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',
}
contents={}
for rel,expected in PINS.items():
    raw=(TASK/rel).read_bytes()
    if hashlib.sha256(raw).hexdigest()!=expected:raise RuntimeError('pin mismatch '+rel)
    contents[rel]=raw.decode()
assembly=contents['research/current14-literal-port-assembly/Current14LiteralPorts.lean']
client=contents['research/current14-structured-endpoint-draft/StructuredEndpoint.lean']
def imports(text):return [line[7:].strip() for line in text.splitlines() if line.startswith('import ')]
assert imports(assembly)==['DiophantineConsistency.CurrentKernel2011','DiophantineConsistency.CurrentMaskRecipes2011']
assert imports(client)==['Current14LiteralPorts','DiophantineConsistency.IPRAStandardCurrentEndpoint']
reports={'Current14LiteralPorts':['beta_eq','mu_eq','omega_eq','K_eq','all_ports'],
         'Current14StructuredEndpoint':['recipe_endpoint']}
for prefix,names in reports.items():
    text=assembly if prefix=='Current14LiteralPorts' else client
    for n in names:
        assert '#print axioms '+(prefix+'.' if prefix=='Current14LiteralPorts' else '')+n in text
wd=TASK/'research/current14-standard-fresh-rebuild-preflight/run-observation.json'
base=json.loads(wd.read_text()) if wd.is_file() else {}
extension=Path('/tmp/current14-printed-port-extension-20261104/state.json')
ext=json.loads(extension.read_text()) if extension.is_file() else {}
print(json.dumps({'status':'SOURCE_INTERFACE_ONLY','source_pins':PINS,'assembly_imports':imports(assembly),
                  'client_imports':imports(client),'expected_axiom_declarations':reports,
                  'base_recorded_status':base.get('status'),'base_recorded_exit':base.get('exit'),
                  'extension_state_present':extension.is_file(),'extension_recorded_status':ext.get('status'),
                  'readiness':'NOT_AUTHENTICATED_OR_LAUNCHED',
                  'scope':'Source shape and instantaneous state only; no Lean, process-exit verification or provider authentication.'},
                 indent=2,sort_keys=True))
