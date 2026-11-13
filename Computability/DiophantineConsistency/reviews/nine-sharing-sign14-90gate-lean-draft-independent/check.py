#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-94gate-lean-draft/Sign14Optimized94.lean';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p)=='ce02afce038ddf7b681e2bd894bc841ddaba7999333cdfcaa3e585cfdc56976f';s=p.read_text();assert not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
seed=root/'research/nine-sharing-sign14-94gate-candidate/seed.json';assert sha(seed)=='ea47ff1c96d90b3d66d26937a948706149bea8602aa88166dba33b27b59d3c3c';candidate=json.loads(seed.read_text());staged=root/'research/nine-sharing-sign14-staged-syntax-draft';staged_manifest={x['module'].split('.')[-1]:x for x in json.loads((root/'research/nine-sharing-sign14-staged-syntax-check/source-manifest.json').read_text())['rows']};defs={};raw={}
for i in range(9):
 q=staged/f'SharingSeed14Shared{i:02}.lean';assert sha(q)==staged_manifest[q.stem]['source_sha256'];t=q.read_text()
 for k,v in re.findall(r'^def (shared\d\d) \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.+)$',t,re.M):raw[k]=v
for i in range(5):
 q=staged/f'SharingSeed14Row{i:02}.lean';assert sha(q)==staged_manifest[q.stem]['source_sha256'];t=q.read_text();k,v=re.search(r'^def (row\d\d) \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.+)$',t,re.M).groups();raw[k]=v
assert len(raw)==49
def parse(text,local=None):
 text=re.sub(r'Expr\.constant\s*\(p\s+(\d+)\)',r'P\1',text);text=re.sub(r'Expr\.constant\s*\((\d+)\s*:\s*ℤ\)',r'N\1',text);text=re.sub(r'Expr\.constant\s+(\d+)',r'N\1',text);text=re.sub(r'Expr\.var\s+(\d+)',r'V\1',text);text=re.sub(r"shared(\d\d)('{0,2})\s+p",lambda m:'S'+m.group(1)+('p'*len(m.group(2))),text)
 text=re.sub(r'center\s+p', 'Scenter', text);toks=re.findall(r'Scenter|S\d\dp{0,2}|[PNV]\d+|[a-z]|[()+*\-]',text);assert ''.join(toks)==re.sub(r'\s+','',text),(text,toks);i=0
 def atom():
  nonlocal i
  x=toks[i];i+=1
  if x=='(':v=expr(0);assert toks[i]==')';i+=1;return v
  if x=='Scenter':return resolve('center')
  if x[0]=='S':return resolve('shared'+x[1:3]+("'"*x.count('p')))
  if x[0] in 'PNV':return ({'P':'port','N':'num','V':'var'}[x[0]],{'P':['beta','K0','MC','MF'][int(x[1:])] if x[0]=='P' else None,'N':int(x[1:]),'V':int(x[1:])}[x[0]])
  assert local is not None and x in local;return local[x]
 def expr(minp):
  nonlocal i
  x=atom()
  while i<len(toks) and toks[i] in '+-*' and (pr:=({'+' :1,'-':1,'*':2}[toks[i]]))>=minp:
   op=toks[i];i+=1;y=expr(pr+1);x=({'+':'add','-':'sub','*':'mul'}[op],x,y)
  return x
 z=expr(0);assert i==len(toks),(text,toks,i);return z
def resolve(k):
 if k not in defs:defs[k]=parse(raw[k])
 return defs[k]
# Parse both independently pinned 95 and proposed 94 shared nodes.
prior=root/'research/nine-sharing-sign14-95gate-lean-draft/Sign14Optimized95.lean'
assert sha(prior)=='5cf5877214c33c448390b3d6db9c7981a3bb6de4b3a2b885d0fc1c7a052a6700'
t95=prior.read_text()
for k,v in re.findall(r"^def (shared\d\d') \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) := (.+)$",t95,re.M):raw[k]=v
assert len([k for k in raw if k.endswith("'")])==7
for k,v in re.findall(r"^def (shared\d\d'') \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) := (.+)$",s,re.M):raw[k]=v
assert {k for k in raw if k.endswith("''")}=={"shared41''","shared42''","shared43''"}
raw['center']=re.search(r'^def center \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.+)$',s,re.M).group(1)
for i in (0,4):raw[f"row{i:02}''"]=re.search(r"def row"+f'{i:02}'+r"'' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.+)",s).group(1)
body=re.search(r"def row03'' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n(.*?)(?=\ndef |\nsection )",s,re.S).group(1);lines=[x.strip() for x in body.strip().splitlines()];loc={}
for line in lines[:-1]:
 m=re.fullmatch(r'let ([a-z])(?: : Expr \(Fin 15\))? := (.+)',line);assert m,line;loc[m.group(1)]=parse(m.group(2),loc)
defs["row03''"]=parse(lines[-1],loc)
# The 95-gate row02 is retained literally in the proposed sum.
body=re.search(r"def row02' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n(.*?)(?=\ndef |\nsection )",t95,re.S).group(1);lines=[x.strip() for x in body.strip().splitlines()];loc={}
for line in lines[:-1]:
 m=re.fullmatch(r'let ([a-z])(?: : Expr \(Fin 15\))? := (.+)',line);assert m,line;loc[m.group(1)]=parse(m.group(2),loc)
defs["row02'"]=parse(lines[-1],loc)

# Extend independently parsed 94-gate graph with the seven proposed 93 nodes.
p93=root/'research/nine-sharing-sign14-93gate-lean-draft/Sign14Optimized93.lean';assert sha(p93)=='4f717d88e562ac71bf69c444cc5cdfeb11b41b6bcaa2308c4517ac1dd9c653a2';z=p93.read_text();assert not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',z)
for k,expr in re.findall(r"^def (shared\d\d') \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) := (.+)$",z,re.M):
 assert k not in raw;raw[k]=expr
raw["shared35'"]=re.search(r"^def shared35' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.+)$",z,re.M).group(1)
assert all(f"shared{i:02}'" in raw for i in (25,30,34,35,36,37))
body=re.search(r"def shared14' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n(.*?)(?=\ndef )",z,re.S).group(1);lines=[x.strip() for x in body.strip().splitlines()];m=re.fullmatch(r'let ([a-z]) : Expr \(Fin 15\) := (.+)',lines[0]);assert m;defs["shared14'"]=parse(lines[1],{m.group(1):parse(m.group(2))})
body=re.search(r"def row01' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n(.*?)(?=\ndef )",z,re.S).group(1);defs["row01'"]=parse(' '.join(body.split()))
body=re.search(r"def row03' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n(.*?)(?=\nsection )",z,re.S).group(1);lines=[x.strip() for x in body.strip().splitlines()];m=re.fullmatch(r'let ([a-z]) : Expr \(Fin 15\) := (.+)',lines[0]);assert m;defs["row03'"]=parse(lines[1].replace('Sign14Optimized94.',''),{m.group(1):parse(m.group(2))})

p92=root/'research/nine-sharing-sign14-92gate-lean-draft/Sign14Optimized92.lean';assert sha(p92)=='4c87b2aed1a494f38fdff4d629808e972958c3ed339bd932240e85c3f0b6c937';w=p92.read_text();assert not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',w)
body=re.search(r"def row02' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n(.*?)(?=\ntheorem )",w,re.S).group(1);lines=[x.strip() for x in body.strip().splitlines()];loc={}
for line in lines[:-1]:
 m=re.fullmatch(r'let ([a-z])(?: : Expr \(Fin 15\))? := (.+)',line);assert m,line;loc[m.group(1)]=parse(m.group(2),loc)
defs['row02_92']=parse(lines[-1],loc)

p90=root/'research/nine-sharing-sign14-90gate-lean-draft/Sign14Optimized90.lean';assert sha(p90)=='78910b0c44cd63d84a4936bf830a743745588fc52aaa45e37c589c40b8e04584';w=p90.read_text();assert not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',w)
# 90 shared14' aliases the previously parsed 93 shared14'; every other shared definition is new.
assert "def shared14' (p : Fin 4 → ℤ) : Expr (Fin 15) := Sign14Optimized93.shared14' p" in w
for k,expr in re.findall(r"^def (shared\d\d') \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) := (.+)$",w,re.M):
 if k!="shared14'":raw[k]=expr;defs.pop(k,None)
raw["shared35'"]=re.search(r"^def shared35' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.+)$",w,re.M).group(1);defs.pop("shared35'",None)
assert all(f"shared{i:02}'" in raw for i in (25,27,30,34,35,36,37))
body=re.search(r"def row01' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n(.*?)(?=\ndef )",w,re.S).group(1);defs["row01'"]=parse(' '.join(body.split()))
body=re.search(r"def row03' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n(.*?)(?=\nsection )",w,re.S).group(1);lines=[x.strip() for x in body.strip().splitlines()];m=re.fullmatch(r'let ([a-z]) : Expr \(Fin 15\) := (.+)',lines[0]);assert m;defs["row03'"]=parse(lines[1].replace('Sign14Optimized94.',''),{m.group(1):parse(m.group(2))})
seed90=root/'research/nine-sharing-sign14-90gate-candidate/seed.json';assert sha(seed90)=='8d42e6e9dfbbf47431ef25963965174f4746de4104a92db569a57d933d4c50c3';c90=json.loads(seed90.read_text())
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
for i in range(5):
 key={0:"row00''",1:"row01'",2:'row02_92',3:"row03'",4:"row04''"}[i];assert resolve(key)==tup(c90['residuals'][i]['expr']),i
assert 'variable {R : Type*} [CommRing R]' in w and all(f'theorem {k}_eval' in w for k in ('shared27','shared25','shared30','shared34','shared35','shared36','shared37','row01','row03','seed'))
for t in ("Sign14Optimized94.row00'' p * Sign14Optimized94.row00'' p", "[row01' p, Sign14Optimized92.row02' p, row03' p,", "Sign14Optimized94.row04'' p]", '(seed p).evalRing v = (Sign14Optimized92.seed p).evalRing v'):assert t in w
for f in ('nine-sharing-sign14-90gate-candidate-independent','nine-sharing-sign14-92gate-lean-draft-independent','nine-sharing-sign14-staged-syntax-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_SOURCE_STRUCTURE','expanded_rows':5,'scope':'unchecked Lean draft AST matches external 90-gate candidate; elaboration and proofs not checked'},indent=2))
