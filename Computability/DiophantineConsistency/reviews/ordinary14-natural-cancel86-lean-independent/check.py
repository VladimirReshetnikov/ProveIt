#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-natural-cancel86-lean-draft';C=D/'research/ordinary14-root74-natural-cancel86/candidate.json';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'cb8a6215470c45726ddefcb189cbbc9462da3771ea21034f4e44aed168ce4d9a',A/'P86NaturalCancel.lean':'57015ecd6c66b06867dc05fe392cf02db4a125e646faf9ca16830cb3c0b0b2ef',A/'make_graph.py':'ce4db629468cb77db05cbb3bc2dc38af4c9fd5577924b603427f880fa6db53b3',A/'observation.json':'8273e96f792e7804da8dfbf28dec192dfbda4f81e9e9f0980ba869158bf720b9',C:'0211a1bcac635af617090facdc3b7f98d18ad94579027df840532d87ae5a5170'}
tail=b"\nIndependent source review: [literal natural cancel-86 graph](../../reviews/ordinary14-natural-cancel86-lean-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='1d7fd6d23dc81006dddbb414783e8848af5a1fa11120fac3a2283e3ed8c2a929'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert H(p)==h,(str(p),H(p),h)
g=json.loads(C.read_bytes());src=(A/'P86NaturalCancel.lean').read_text();assert g['domain']=='nonnegative integers' and g['operations']==len(g['source'])==86 and g['output']=='out'
inputs=['n_J','n_F','n_alpha','n_f','n_i','n_T','n_w','n_s','n_r','n_eta','n_zeta','n_y','n_gamma','n_h'];ports=['beta','K0','MC','MF'];assert g['witnesses']==inputs and g['fixed_numerals']==ports
aliases=re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.var (\d+)$',src,re.M);assert aliases==[(n,str(i)) for i,n in enumerate(inputs)]
port_aliases=re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.constant \(p (\d+)\)$',src,re.M);assert port_aliases==[(n,str(i)) for i,n in enumerate(ports)]
lo='  -- BEGIN LITERAL GRAPH\n';hi='  -- END LITERAL GRAPH\n';assert src.count(lo)==src.count(hi)==1
body=src.split(lo,1)[1].split(hi,1)[0];lines=body.splitlines();assert len(lines)==86
pattern=re.compile(r'^  let ([A-Za-z][A-Za-z0-9_]*) := ([A-Za-z0-9_]+) ([+*\-]) ([A-Za-z0-9_]+)$')
def atom(x):return int(x) if x.isdecimal() else x
rows=[]
for line in lines:
 m=pattern.fullmatch(line);assert m,line;n,x,op,y=m.groups();rows.append([n,op,atom(x),atom(y)])
assert rows==g['source']
fields=['first','main','aux','strong','guardFactor','output','qF','C','G','rank'];nodes=['F0','F1','Fa','Fs','guard','out','qF','C','G','R']
block=src.split('structure Graph where\n',1)[1].split('\nset_option ',1)[0];assert re.findall(r'^  (\w+) : Expr \(Fin 14\)$',block,re.M)==fields
assert src.count('  ⟨'+', '.join(nodes)+'⟩')==1
by={n:[op,x,y] for n,op,x,y in rows};assert by['P01']==['*','F0','F1'] and by['P012']==['*','P01','Fa'] and by['P0123']==['*','P012','Fs'] and by['P01234']==['*','P0123','guard'] and by['out']==['-','P01234',1]
assert re.search(r'theorem output_shape \(p : Fin 4 → ℤ\) : \(graph p\)\.output =\s*\(graph p\)\.first \* \(graph p\)\.main \* \(graph p\)\.aux \*\s*\(graph p\)\.strong \* \(graph p\)\.guardFactor - 1 := by rfl',src)
known=set(inputs+ports)
for n,op,x,y in rows:
 assert n not in known and all(type(a) is int or a in known for a in (x,y));known.add(n)
needed={'out'}
for n,op,x,y in reversed(rows):
 if n in needed:needed.update(a for a in (x,y) if isinstance(a,str))
assert all(n in needed for n,_,_,_ in rows) and set(inputs+ports)<=needed
rng=random.Random(860141);controls=0
for modulus in (4,12,17):
 for _ in range(100):
  init={k:rng.randrange(-9,10) for k in inputs+ports}
  def calc(rws):
   v=init.copy()
   for n,op,x,y in rws:
    a=x if type(x) is int else v[x];b=y if type(y) is int else v[y]
    v[n]=({'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]())%modulus
   return v
  lhs,rhs=calc(rows),calc(g['source']);assert all(lhs[n]==rhs[n] for n,_,_,_ in rows);controls+=1
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'make_graph.py'),'--check'],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
prior=D/'reviews/ordinary14-root74-natural-cancel86-independent';r=subprocess.run([sys.executable,'-I','-S','-B',str(prior/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(prior/'observation.json').read_bytes()
print(json.dumps({'scope':'literal source/graph mapping and finite ring controls; no Lean or file binding','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'rows':len(rows),'slots':len(inputs),'ports':len(ports),'fields':dict(zip(fields,nodes)),'modular_controls':controls,'generator_receipt_replayed':True,'independent_external_graph_receipt_replayed':True},sort_keys=True,indent=2))
