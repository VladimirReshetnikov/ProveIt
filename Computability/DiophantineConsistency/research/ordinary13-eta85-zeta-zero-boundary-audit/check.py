from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta85-zeta-zero-boundary-audit')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(D/'generate.py')])==(D/'generator-receipt.json').read_bytes()
old=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());new=json.loads((D/'probe.json').read_text())
assert len(old['source'])==len(new['source'])==85
assert old['witnesses']==new['witnesses'] and old['fixed_numerals']==new['fixed_numerals']
seen=set(new['witnesses']+new['fixed_numerals'])
for n,op,a,b in new['source']:
 assert n not in seen and op in '+-*' and (isinstance(a,int) or a in seen) and (isinstance(b,int) or b in seen)
 seen.add(n)
assert new['output'] in seen

def ev(g,w,p,mod=None):
 d=dict(zip(g['witnesses'],w));d.update(zip(g['fixed_numerals'],p))
 for n,op,a,b in g['source']:
  x=d[a] if isinstance(a,str) else a;y=d[b] if isinstance(b,str) else b
  z={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
  d[n]=z if mod is None else z%mod
 return d
for t in range(160):
 w=[(t*(i+3)+i*i)%9 for i in range(13)];p=[(t*(j+2)+j)%9-4 for j in range(4)]
 shifted=w.copy();shifted[10]+=1
 assert ev(old,w,p,1000000007)['out']==ev(new,shifted,p,1000000007)['out']
# Exact entire-graph zeros, all witness coordinates natural, but signed ports
# violate compact-port requirements. No external fixed-port conclusion.
cases=[{'witness':[1,0,0,1,0,0,0,0,0,0,0,1,0], 'ports':[-1,0,1,0], 'violation':'beta=-1'},
       {'witness':[1,0,0,1,0,0,1,0,0,0,0,1,0], 'ports':[0,-2,-1,0], 'violation':'K0=-2 and MC=-1'}]
results=[]
for case in cases:
 w,p=case['witness'],case['ports'];assert min(w)>=0 and w[10]==0
 e=ev(new,w,p); assert e['A0']==e['A1']==e['g72']==0 and e['Fa']==1 and e['out']==0
 # The same witness in the old graph has zeta=1, not the probe's zero.
 before=ev(old,w,p); assert before['out']!=0
 results.append({'witness':w,'ports':p,'violations':case['violation'],'q':e['q'],'Y':e['Y'],'Bt':e['Bt'],'R':e['R'],'Z':e['Z'],'Dstar':e['Dstar'],'A0':e['A0'],'A1':e['A1'],'Fa':e['Fa'],'g72':e['g72'],'probe_output':e['out'],'parent_same_witness_output':before['out']})
src=Path('research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src').read_text()
assert 'def ports (K : ℕ) : Fin 4 → ℕ' in src
print(json.dumps({'exact_parent_shift_controls':160,'probe_rows':len(new['source']),'full_zero_signed_port_examples':results,'compact_port_full_zero_found':False,'compact_scope':'Not searched or disproved; both witnesses use a negative port.','lean_executed':False},sort_keys=True,indent=2))
