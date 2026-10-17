#!/usr/bin/env python3
from pathlib import Path
from collections import defaultdict
from types import SimpleNamespace
import sys,json
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source/Computability/BusyBeaver/Research/ZFC'))
import candidate252_independent_audit as audit
source=ROOT/'source/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
sys.modules['cost_search']=SimpleNamespace()
ns={'__name__':'strict_gap43'}
raw=source.read_text().replace('40-len(pc)','43-len(pc)')
assert raw!=source.read_text()
exec(compile(raw,str(source),'exec'),ns)
src=ROOT/'compression/mp_newperm_native';out=ROOT/'compression/mp_newperm_gap43_native';out.mkdir(exist_ok=True)
table={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in audit.read_table((src/'native_table.txt').read_bytes()).items()}
class Tracking(dict):
 def __init__(self,x):super().__init__(x);self.used=set()
 def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)
rows=[];usage=defaultdict(set)
for line in (src/'native_cases.txt').read_text().splitlines():
 fields=line.split();i=int(fields[0]);pc=fields[1];phys=int(fields[2]);zero=int(fields[3]);nxt=fields[4];overflow=int(fields[5]);effect=int(fields[6]);register=int(fields[7]);halt=int(fields[8])
 branch=(phys,bool(zero)) if phys>=0 else None
 eff=('inc' if effect==0 else 'dec',register) if effect>=0 else None
 target=[] if nxt=='-' else [('b',int(c)) for c in nxt]
 target += [('r',0,1,43+overflow-(0 if nxt=='-' else len(nxt))),('b',1),('box',('plain',eff))]
 current=Tracking(table);rules,literal=ns['run'](current,pc,branch,ns['canon']([('b',1)],target),halt=bool(halt),fuel=1000)
 assert literal>0
 fields[-1]=str(sum(rules.values()));rows.append(' '.join(fields))
 for key in current.used:usage[key].add(i)
(out/'native_table.txt').write_bytes((src/'native_table.txt').read_bytes());(out/'native_cases.txt').write_text('\n'.join(rows)+'\n')
with (out/'native_usage.txt').open('w') as f:
 for (q,b),indices in sorted(usage.items(),key=lambda x:(int(x[0][0]),x[0][1])):f.write(f'{q} {b} '+','.join(map(str,sorted(indices)))+'\n')
meta=json.loads((src/'metadata.json').read_text());meta['minimum_gap']=43;meta['baseline_cases_checked']=len(rows)
(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
phase=ROOT/'compression/mp_newperm_gap43_phase_native';phase.mkdir(exist_ok=True)
for name in ('native_table.txt','native_usage.txt'):(phase/name).write_bytes((out/name).read_bytes())
(phase/'native_cases.txt').write_text('\n'.join(r for r in rows if int(r.split()[0]) not in {8202,8203,8204})+'\n')
meta['excluded_phase_cases']=[8202,8203,8204];(phase/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
print('Gap43 original + phase-filtered inputs independently checked.')
