#!/usr/bin/env python3
"""Independent row, slot, liveness and signed guard-shift review; no Lean."""
from pathlib import Path
import hashlib,json,re,random,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1]; A=D/'research/ordinary14-unit75-guard74-lean-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'README.md':'5000379da8e4fa734a0ecdf6f021d1486ad1592dc1ba4ac5c1c512accb488b28','P75NegativePell.lean':'1ef538a3af4f2c1bb162fe335683d6522a6744831168c94b79132646f3496dbe','P74PositiveGuard.lean':'5c441b8df055693e745967f01ef8128d808f5915e3cffb906473499745c4c11b','make_graph.py':'c95e5102f34f79883f789e58230e2f0cfb721b2a8911091e3e3441e0567b52bf','observation.json':'083fa7cd3a01541f7f5ce84bc29f1c4eef308ae431fb3625fd014ac5c0d61f2e'}
tail=b"\nIndependent source review: [75/74 literal graphs](../../reviews/ordinary14-unit75-guard74-lean-independent/README.md).\n"
final=(A/'README.md').read_bytes()
assert hashlib.sha256(final).hexdigest()=='c723d05310de395ebf7df595202d6a5843fc9ec3f652226064645a9c43da37cc'
assert final.endswith(tail) and hashlib.sha256(final[:-len(tail)]).hexdigest()==pins['README.md']
for name,want in pins.items():
 if name!='README.md':assert sha(A/name)==want,name
candidates=[D/'research/ordinary14-negative-pell75/candidate.json',D/'research/ordinary14-positive-guard74/candidate.json']
assert [sha(p) for p in candidates]==['89a9a0217d28d655fbf2592d995f4d766175a45560fa4d33b251dd3711e5b1c1','e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093']
objs=[json.loads(p.read_text()) for p in candidates]
witness=['J','F','alpha','f','i','T','w','s','r','eta','zeta','y','gamma','h'];ports=['beta','K0','MC','MF']
fields=['first','main','aux','strong','guardFactor','output','b','q','X','Y','k','ell','a','c','U','Dstar','Q','I','vroot','C']
common=['F0','F1','Fa','Fs',None,'out','qm','q','X','Y','k','ell','a','c','U','Dstar','Q','I','V','C']
for obj,name,count,guard in zip(objs,['P75NegativePell','P74PositiveGuard'],[75,74],['Fg','guard']):
 text=(A/(name+'.lean')).read_text();assert obj['witnesses']==witness and obj['fixed_numerals']==ports
 for j,w in enumerate(witness):assert f'  let {w} : Expr (Fin 14) := .var {j}\n' in text
 for j,w in enumerate(ports):assert f'  let {w} : Expr (Fin 14) := .constant (p {j})\n' in text
 got_fields=re.findall(r'^  ([A-Za-z][A-Za-z0-9_]*) : Expr \(Fin 14\)$',text,re.M);assert got_fields==fields
 body=text.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH\n',1)[0]
 rows=[]
 for line in body.splitlines():
  m=re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := ([A-Za-z0-9_]+) ([+*\-]) ([A-Za-z0-9_]+)',line);assert m,line
  n,a,op,b=m.groups();rows.append([n,op,int(a) if a.isdigit() else a,int(b) if b.isdigit() else b])
 assert rows==obj['source'] and len(rows)==obj['operations']==count
 available=set(witness+ports);defs={}
 for n,op,a,b in rows:
  assert n not in available and op in '+-*'
  for x in (a,b):assert isinstance(x,int) or x in available
  available.add(n);defs[n]=(a,b)
 live=set();stack=['out']
 while stack:
  n=stack.pop()
  if not isinstance(n,str) or n in live:continue
  live.add(n)
  if n in defs:stack.extend(defs[n])
 assert set(defs).issubset(live) and set(witness+ports).issubset(live)
 expected=[guard if n is None else n for n in common]
 assert '  ⟨'+', '.join(expected)+'⟩' in text
 assert '(graph p).first * (graph p).main * (graph p).aux *\n      (graph p).strong * (graph p).guardFactor - 1 := by rfl' in text
left={r[0]:r for r in objs[0]['source']};right={r[0]:r for r in objs[1]['source']}
assert set(left)-set(right)=={'Fg'} and not (set(right)-set(left))
assert {k for k in left.keys()&right.keys() if left[k]!=right[k]}=={'guard_base','P01234'}
assert left['guard_base']==['guard_base','-','g27','F'] and right['guard_base']==['guard_base','+','g27','qF']
assert left['P01234']==['P01234','*','P0123','Fg'] and right['P01234']==['P01234','*','P0123','guard']
def evaluate(obj,values):
 z=values.copy()
 for n,op,a,b in obj['source']:
  a=z[a] if isinstance(a,str) else a;b=z[b] if isinstance(b,str) else b
  z[n]={'+' : lambda:a+b, '-' : lambda:a-b,'*':lambda:a*b}[op]()
 return z
rng=random.Random(740075)
for _ in range(256):
 args={k:rng.randrange(-3,4) for k in witness+ports}
 shifted=args.copy();shifted['h']+=1
 x=evaluate(objs[0],args);y=evaluate(objs[1],shifted)
 for n in ['F0','F1','Fa','Fs','out']:assert x[n]==y[n],n
 assert x['Fg']==y['guard']
author=subprocess.run([sys.executable,'-I','-S','-B',str(A/'make_graph.py'),'--check'],cwd=D,check=True,capture_output=True).stdout
assert author==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'independent static source/row audit and finite signed controls; no Lean, provider or graph equivalence theorem','author_pins':pins,'candidate_sha256':[sha(p) for p in candidates],'operation_rows':[75,74],'live_inputs':[14,14],'live_ports':[4,4],'signed_guard_shift_controls':256,'author_receipt_reproduced':True},sort_keys=True,indent=2))
