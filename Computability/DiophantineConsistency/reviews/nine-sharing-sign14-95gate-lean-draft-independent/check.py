#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-95gate-lean-draft/Sign14Optimized95.lean';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p)=='5cf5877214c33c448390b3d6db9c7981a3bb6de4b3a2b885d0fc1c7a052a6700';s=p.read_text();assert not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
seed=root/'research/nine-sharing-sign14-95gate-candidate/seed.json';assert sha(seed)=='b00a2d0c4d0c3a25dc7c8fdd2e41690bdaab0315b4f9c4586e9e067c577f1439';candidate=json.loads(seed.read_text());staged=root/'research/nine-sharing-sign14-staged-syntax-draft';staged_manifest={x['module'].split('.')[-1]:x for x in json.loads((root/'research/nine-sharing-sign14-staged-syntax-check/source-manifest.json').read_text())['rows']};defs={};raw={}
for i in range(9):
 q=staged/f'SharingSeed14Shared{i:02}.lean';assert sha(q)==staged_manifest[q.stem]['source_sha256'];t=q.read_text()
 for k,v in re.findall(r'^def (shared\d\d) \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.+)$',t,re.M):raw[k]=v
for i in range(5):
 q=staged/f'SharingSeed14Row{i:02}.lean';assert sha(q)==staged_manifest[q.stem]['source_sha256'];t=q.read_text();k,v=re.search(r'^def (row\d\d) \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.+)$',t,re.M).groups();raw[k]=v
assert len(raw)==49
def parse(text,local=None):
 text=re.sub(r'Expr\.constant\s*\(p\s+(\d+)\)',r'P\1',text);text=re.sub(r'Expr\.constant\s*\((\d+)\s*:\s*ℤ\)',r'N\1',text);text=re.sub(r'Expr\.constant\s+(\d+)',r'N\1',text);text=re.sub(r'Expr\.var\s+(\d+)',r'V\1',text);text=re.sub(r"shared(\d\d)('?)\s+p",lambda m:'S'+m.group(1)+('p' if m.group(2) else ''),text)
 toks=re.findall(r'S\d\dp?|[PNV]\d+|[a-z]|[()+*\-]',text);assert ''.join(toks)==re.sub(r'\s+','',text),(text,toks);i=0
 def atom():
  nonlocal i
  x=toks[i];i+=1
  if x=='(':v=expr(0);assert toks[i]==')';i+=1;return v
  if x[0]=='S':return resolve('shared'+x[1:3]+("'" if x.endswith('p') else ''))
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
# Optimized shared definitions are parsed independently and expanded recursively.
for k,v in re.findall(r"^def (shared\d\d') \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) := (.+)$",s,re.M):raw[k]=v
assert {k for k in raw if k.endswith("'")}=={f"shared{i:02}'" for i in (7,32,38,39,41,42,43)}
for i in (0,4):
 pat=r"def row"+f'{i:02}'+r"' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.+)";raw[f"row{i:02}'"]=re.search(pat,s).group(1)
# Parse local let bindings in the two remaining rewritten rows.
for i in (2,3):
 body=re.search(r"def row"+f'{i:02}'+r"' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n(.*?)(?=\ndef |\nsection )",s,re.S).group(1);lines=[x.strip() for x in body.strip().splitlines()];loc={}
 for line in lines[:-1]:
  m=re.fullmatch(r'let ([a-z])(?: : Expr \(Fin 15\))? := (.+)',line);assert m,line;loc[m.group(1)]=parse(m.group(2),loc)
 defs[f"row{i:02}'"]=parse(lines[-1],loc)
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
for i in range(5):
 actual=resolve('row01' if i==1 else f"row{i:02}'");assert actual==tup(candidate['residuals'][i]['expr']),i
assert 'variable {R : Type*} [CommRing R]' in s and all(f'theorem {k}_eval' in s for k in ('shared07','shared32','shared38','shared39','shared41','shared42','shared43','row00','row02','row03','row04','seed'))
assert "row00' p * row00' p" in s and "[row01 p, row02' p, row03' p, row04' p]" in s
for f in ('nine-sharing-sign14-95gate-candidate-independent','nine-sharing-sign14-staged-syntax-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_SOURCE_STRUCTURE','expanded_rows':5,'changed_shared':7,'scope':'unchecked Lean draft AST matches external 95-gate candidate; proofs/elaboration and JSON binding unverified'},indent=2))
