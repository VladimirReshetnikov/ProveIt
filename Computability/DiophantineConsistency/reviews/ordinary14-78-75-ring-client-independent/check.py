#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-78-75-ring-client-draft'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'fb29cf10cb4a993c6afe11979b9e85bcfe510070dd449affe9470bb60593d3d2',A/'Ring78To75.lean':'792a773184ef790ec0a168a82ad32417db896e22f6f08c0e23cd502340d0cbdc',A/'check_source.py':'35eb73037231ba1856595e6f36937ab3ab24c9b9badf86cc04aefbbc51b69a48',A/'observation.json':'2cbb99e32b5c322bdab36c0dea6769894bdfb4edb7562a331931af56d057b158'}
tail=b"\nIndependent source review: [78/75 ring factor identities](../../reviews/ordinary14-78-75-ring-client-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='a2cf14d539690fa27685d3367f7a5a49e6f7e743e4875ba1d0ad438f1b75c341'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert H(p)==h,(str(p),H(p),h)
def calc(g,vals,n):
 vals=vals.copy()
 for name,op,x,y in g['source']:
  x=vals[x] if isinstance(x,str) else x;y=vals[y] if isinstance(y,str) else y
  vals[name]=({'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]())%n
 return vals
old=json.loads((D/'research/ordinary14-aux-root78/candidate.json').read_bytes());new=json.loads((D/'research/ordinary14-negative-pell75/candidate.json').read_bytes())
assert old['witnesses']==new['witnesses'] and old['fixed_numerals']==new['fixed_numerals']
rows1={r[0]:r[1:] for r in old['source']};rows2={r[0]:r[1:] for r in new['source']}
def deps(rows,name):
 if not isinstance(name,str) or name not in rows:return ('leaf',name)
 op,x,y=rows[name];return (op,deps(rows,x),deps(rows,y))
for name in ('A1','Fa','g72','guard','g38','g40'):assert deps(rows1,name)==deps(rows2,name),name
assert rows1['g41']==['+',1,'g40'] and rows1['A0']==['-','g38','g41'] and rows2['F0']==['-','g38','g40']
assert rows2['F1']==['+',1,'A1'] and rows2['Fs']==['+',1,'g72'] and rows2['Fg']==['+',1,'guard']
rng=random.Random(45178);counts={}
for modulus in (4,12,17):
 for _ in range(200):
  vals={name:rng.randrange(-9,10) for name in old['witnesses']+old['fixed_numerals']};a=calc(old,vals,modulus);b=calc(new,vals,modulus)
  assert [b['F0'],b['F1'],b['Fa'],b['Fs'],b['Fg']]==[(1+a['A0'])%modulus,(1+a['A1'])%modulus,a['Fa'],(1+a['g72'])%modulus,(1+a['guard'])%modulus]
 counts[str(modulus)]=200
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'source and literal DAG plus finite ring controls only; no Lean or model endpoint','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'modular_controls':counts,'author_receipt_replayed':True},sort_keys=True,indent=2))
