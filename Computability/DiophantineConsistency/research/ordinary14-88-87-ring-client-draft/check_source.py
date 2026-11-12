from pathlib import Path
import hashlib,json,random
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
old=json.loads((D/'research/ordinary14-guarded-fold88-26/candidate.json').read_bytes())
new=json.loads((D/'research/ordinary14-shifted-guard87-probe/candidate.json').read_bytes())
assert len(old['source'])==88 and len(new['source'])==87
assert old['witnesses'][:-1]==new['witnesses'][:-1] and old['witnesses'][-1]=='t' and new['witnesses'][-1]=='omega'
expect=[]
for row in old['source']:
 if row[0]=='g28':expect.append(['guard_base','-','g27','F'])
 elif row[0]=='Bt':continue
 elif row[0]=='bt_quotient':expect.append(['bt_quotient','*','qm','omega'])
 elif row[0]=='guard':expect.append(['guard','-','guard_base','bt_quotient'])
 else:expect.append(row)
assert new['source']==expect
def evaluate(g,inp,ports):
 v=dict(zip(g['witnesses'],inp));v.update(dict(zip(g['fixed_numerals'],ports)))
 def val(x):return x if isinstance(x,int) else v[x]
 for n,op,a,b in g['source']:
  x,y=val(a),val(b);v[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(83187)
for _ in range(500):
 x=[rng.randrange(-3,4) for _ in range(14)];ports=[rng.randrange(-3,4) for _ in range(4)]
 y=x.copy();y[13]=x[13]+x[1]
 a=evaluate(old,x,ports);b=evaluate(new,y,ports)
 for field in ('A0','A1','Fa','g72','guard','guarded_out'):assert a[field]==b[field],field
s=(P/'RingComparison88To87.lean').read_text()
for t in ('Function.update v 13 (v 13+v 1)','theorem guard_cut','theorem output_eval','P88QuotientGuarded.output_shape','P87ShiftedGuard.output_shape'):assert t in s
print(json.dumps({'literal_delta_verified':True,'signed_graph_controls':500,'lean_run':False,'source_sha256':hashlib.sha256((P/'RingComparison88To87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
