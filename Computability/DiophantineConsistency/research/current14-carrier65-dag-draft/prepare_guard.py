#!/usr/bin/env python3
"""Prepare a three-stage guard; this script does not invoke Lean."""
import hashlib
import json
import re
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
check = here.parent / 'current14-carrier65-dag-check'
template = here.parent / 'current14-seed-readable-prefix-staged-check' / 'run.py'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
names = ['ArithmeticDAG', 'Current14Carrier65DAGCore', 'Current14Carrier65DAGValue']
srcdir = check / 'src/DiophantineConsistency'
rows = []
for name in names:
    path = srcdir / (name + '.lean')
    imports = re.findall(r'^import ([A-Za-z0-9_.]+)$', path.read_text(), re.M)
    rows.append({'module': 'DiophantineConsistency.' + name,
                 'source': str(path.relative_to(repo)), 'source_sha256': sha(path),
                 'imports': imports})
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
pkg = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
package_pins = {}
for mod in rows[0]['imports']:
    path = pkg / (mod.replace('.', '/') + '.olean')
    package_pins[mod] = {'realpath': str(path.resolve()), 'sha256': sha(path)}
base = Path('/tmp/nine-sharing-sign17-readable-current14-endpoint-20261110')
carrier = base / 'lib/DiophantineConsistency/Carrier65.olean'
carrier_pin = {'realpath': str(carrier.resolve()), 'sha256': sha(carrier)}
audit = d / 'reviews/current14-carrier65-dag-draft-independent/check.py'
out = template.read_text()
out = out.replace('Bounded order-block client against the audited single-context Fin942 provider.',
                  'Bounded three-stage Carrier65 DAG, count, and semantic-equality client.')
out = out.replace('Audited single-context provider and direct source/object/guard observations; no Lean, complete transitive trace, global order or rank proof.',
                  'Audited provider and guarded staged sources; no Lean theorem or full transitive import trace.')
out = out.replace('/tmp/current14-seed-readable-prefix-staged-20261110',
                  '/tmp/current14-carrier65-dag-check-20261110')
out = out.replace('0d90250f655fa6a12c69cf728895a369209c1267eef1197afc66f2f02b29a3e7', sha(manifest))
start = out.index("witness=D/'research/nine-sharing-sign17-k-ranking-witness/witness.json'")
end = out.index('provider_names={r[\'module\']:r for r in base[\'rows\']}', start)
replacement = f'''draft=D/'research/current14-carrier65-dag-draft/Current14Carrier65DAG.lean'
need(sha(draft)=='{sha(here / 'Current14Carrier65DAG.lean')}','reviewed draft pin')
need(sha(D/'reviews/current14-carrier65-dag-draft-independent/check.py')=='{sha(audit)}','source audit pin')
need(sha(P/'src/DiophantineConsistency/ArithmeticDAG.lean')=='{sha(d / 'Lean/DiophantineConsistency/ArithmeticDAG.lean')}','infrastructure source pin')
reviewed=draft.read_text();cut=reviewed.index('/-- This is the essential bridge')
core=(P/'src/DiophantineConsistency/Current14Carrier65DAGCore.lean').read_text()
value=(P/'src/DiophantineConsistency/Current14Carrier65DAGValue.lean').read_text()
need(core.startswith(reviewed[:cut].replace('import DiophantineConsistency.Carrier65\\n','',1)),'core reviewed declarations')
need(reviewed[cut:reviewed.rindex('\\nend DiophantineConsistency.Current14Carrier65DAG')] in value,'semantic reviewed declaration')
package_pins={package_pins!r}
carrier_pin={carrier_pin!r}
for mod,rec in package_pins.items():
 path=PKG/(mod.replace('.','/')+'.olean');need(path.is_file() and str(path.resolve())==rec['realpath'] and sha(path)==rec['sha256'],'package direct pin '+mod)
carrier=BASE/'lib/DiophantineConsistency/Carrier65.olean'
need(carrier.is_file() and str(carrier.resolve())==carrier_pin['realpath'] and sha(carrier)==carrier_pin['sha256'],'carrier direct pin')
'''
out = out[:start] + replacement + out[end:]
out = out.replace("need(len(entries)==3,'stage count')", "need(len(entries)==3,'stage count')")
out = out.replace("need(m.startswith('DiophantineConsistency.') and (m.split('.')[-1] in provider_names or m.split('.')[-1] in names[:names.index(n)]),'unexpected provider import '+m)",
                  "need(m in package_pins or m=='DiophantineConsistency.Carrier65' or m.split('.')[-1] in names[:names.index(n)],'unexpected direct import '+m)")
old = """if depname in provider_names:expected=provider_names[depname]['object_sha256'];path=BASE/'lib/DiophantineConsistency'/(depname+'.olean')
   else:
    prior=[x for x in state['rows'][:-1] if x['module']==depname];need(len(prior)==1,'local producer '+depname);expected=prior[0]['object_sha256'];path=OUT/'lib/DiophantineConsistency'/(depname+'.olean')
   need(rec['sha256']==expected and rec['realpath']==str(path.resolve()),'direct producer '+mod)"""
new = """if mod in package_pins:
    expected=package_pins[mod]['sha256'];path=Path(package_pins[mod]['realpath'])
   elif mod=='DiophantineConsistency.Carrier65':
    expected=carrier_pin['sha256'];path=Path(carrier_pin['realpath'])
   else:
    prior=[x for x in state['rows'][:-1] if x['module']==depname];need(len(prior)==1,'local producer '+depname);expected=prior[0]['object_sha256'];path=OUT/'lib/DiophantineConsistency'/(depname+'.olean')
   need(rec['sha256']==expected and rec['realpath']==str(path.resolve()),'direct producer '+mod)"""
assert old in out
out = out.replace(old, new)
out = out.replace('PASS quoted arithmetic prefix current14 iPRA endpoint', 'PASS current14 Carrier65 circuit and semantic bridge')
(check / 'run.py').write_text(out)
print('Prepared three stages; no Lean invoked.')
