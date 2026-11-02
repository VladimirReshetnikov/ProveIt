#!/usr/bin/env python3
"""Compare captured full Lean-evaluated ports with all pinned coefficient bytes.

This external audit is not a Lean theorem or a general parser for the TeX
constant recipes. Its direct Lean computation uses the separately audited,
historical author provider and retains its package/dynamic limitations.
"""
import copy
import gzip
import hashlib
import json
from pathlib import Path
import sys

if not __debug__:
    raise RuntimeError('This audit requires assertions; do not run Python with -O or -OO')

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
SNAP = Path('/tmp/ipra-aq29-fresh-source-closure-v2')
PARENT = Path('/tmp/ipra-aq29-fresh-project-pair/author')
PROBE = Path('/tmp/equation14-fixed-port-probe')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
raw_sha = lambda b: hashlib.sha256(b).hexdigest()

json_path = BASE/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
assert H(json_path) == 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
candidate = json.loads(json_path.read_text())
assert candidate['fixed_numerals'] == ['beta','K0','MC','MF']
assert H(HERE/'Probe.lean') == H(PROBE/'Probe.lean') == '4243836992c47380ba3088648013878ad475589730ede3ddfae54b7ae1d17d28'
assert (HERE/'probe.log').read_text() == (PROBE/'probe.log').read_text() == 'WROTE_FOUR_EXACT_DECIMAL_PORTS\n'
assert H(HERE/'deps.log') == H(PROBE/'deps.log') == 'cb27294bd712bbde34bae3b413388966def535bf822c91297a867d6df3906221'
deps = (HERE/'deps.log').read_text().splitlines()
assert deps == ['/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean',
                '/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean',
                '/tmp/ipra-aq29-fresh-project-pair/author/lib/DiophantineConsistency/CurrentKernelData2011.olean']
state = json.loads((PARENT/'state.json').read_text())
assert H(PARENT/'state.json') == 'b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153'
assert state['status'] == 'PASS' and len(state['records']) == 1210
row = next(r for r in state['records'] if r['module'] == 'DiophantineConsistency.CurrentKernelData2011')
src = SNAP/'src/DiophantineConsistency/CurrentKernelData2011.lean'
obj = PARENT/'lib/DiophantineConsistency/CurrentKernelData2011.olean'
assert row['exit'] == 0 and H(src) == row['source_sha256'] == '529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c'
assert H(obj) == row['object_sha256'] == '95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896'
init = Path(deps[0]); assert init.is_file()
assert str(init) in state['guarded_companions'] and state['guarded_companions'][str(init)]['sha256'] == H(init)
assert H(state['lean_path']) == state['lean_sha256']

coefficient_dir = json_path.parent/'coefficients'
result_ports = []
for i, name in enumerate(candidate['fixed_numerals']):
    meta = candidate['coefficient_binding']['ports'][name]
    encoded = (coefficient_dir/meta['file']).read_bytes()
    assert raw_sha(encoded) == meta['gzip_sha256']
    binary = gzip.decompress(encoded)
    assert len(binary) == meta['raw_bytes'] and raw_sha(binary) == meta['raw_sha256']
    decimal = gzip.decompress((HERE/'port-outputs'/f'port{i}.txt.gz').read_bytes())
    assert decimal == (PROBE/f'port{i}.txt').read_bytes()
    assert decimal == str(int.from_bytes(binary,'big')).encode('ascii')
    result_ports.append({'index':i,'name':name,'decimal_digits':len(decimal),
                         'decimal_sha256':raw_sha(decimal),'integer_bytes':len(binary),
                         'integer_sha256':raw_sha(binary),
                         'captured_gzip_sha256':H(HERE/'port-outputs'/f'port{i}.txt.gz')})

# The existing separately reviewed recipe reconstruction pins the entire TeX
# constant block and compares its manually transcribed fixed formulas, decoded
# 942 tiles and 885,481 ranking comparisons to these full coefficient bytes.
# Reproduce its captured JSON and identify the one unrelated stale field in
# its older receipt rather than silently claiming byte identity.
fresh = json.loads((HERE/'printed-constants-repeat.json').read_text())
assert fresh == json.loads((PROBE/'printed-constants-repeat.json').read_text())
old = json.loads((BASE/'research/adaptive-direct-ordinate86/PRINTED-CONSTANTS-AUDIT.json').read_text())
assert fresh['result'] == 'PASS' and fresh['rank_comparisons'] == 885481 and fresh['tile_rows'] == 942
assert fresh['constant_block_sha256'] == 'e5e7b58b54e57badc97ba6ee7f7577ec8e858c88189474723ce28ae629b0a6c6'
assert fresh['source_sha256']['equation.tex'] == '94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635'
for i,name in enumerate(['beta','K','MC','MF_source']):
    assert fresh['fixed_port_records'][name]['sha256'] == result_ports[i]['integer_sha256']
a,b = copy.deepcopy(fresh),copy.deepcopy(old)
current_86 = a['source_sha256'].pop('equation86.tex'); old_86 = b['source_sha256'].pop('equation86.tex')
assert current_86 != old_86 and a == b

report = {'status':'PASS_FOUR_COMPLETE_LEAN_EVALUATED_PORTS',
          'probe_source_sha256':H(HERE/'Probe.lean'),'probe_log_sha256':H(HERE/'probe.log'),
          'probe_deps_sha256':H(HERE/'deps.log'),'printed_recipe_audit_sha256':H(HERE/'printed-constants-repeat.json'),
          'candidate_sha256':H(json_path),'parent_state_sha256':H(PARENT/'state.json'),
          'kernel_data_source_sha256':H(src),'kernel_data_object_sha256':H(obj),
          'ports':result_ports,'printed_ranking_comparisons':fresh['rank_comparisons'],
          'prior_receipt_only_difference':{'field':'source_sha256.equation86.tex','prior':old_86,'current':current_86},
          'scope':'Exact decimal and full coefficient-byte equality for four #eval outputs using the fresh historical author provider. Printed fixed recipes are checked through the pinned, manually transcribed finite reconstruction, not a general TeX parser. No internal Lean equality theorem, dynamic-load trace, or full transitive package authentication is claimed.'}
out = HERE/'ports-receipt.json'; assert not out.exists(); out.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(report['status'],H(out))
