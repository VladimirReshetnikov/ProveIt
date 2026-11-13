#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-sextic-lean-draft';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'SharingSeed28Sextic.lean':'ccc091d8b88f3f165c86fd8308c7ba35217979aa21a6412437a6fb1015394800','SharingSeed28BridgeDraft.lean':'54a5790f5dca97bce9a79cc32b96d7a320195be72f3aec51db59d1cdb9d68e9c','check_bridge.py':'738c2616699e301055d640a1097842cdeefdd25f93180dbb6960e7bbc4a7278e','generate.py':'f9c52ce19d927d1f94d7d694435d4e8b7bf37fc50ff3770a0069a5f336eb6e8d','check.py':'63bab5e5678bd4780425bc0fc0cda7e80f00f70de376dab21e40d0f19cbd8d4f'}.items():assert sha(P/n)==h
old=json.loads((D/'research/nine-sharing-sign31-sextic-candidate/seed.json').read_text());new=json.loads((D/'research/nine-sharing-sign28-sextic-candidate/seed.json').read_text());V=lambda i:['var',i];N=lambda n:['num',n];A=lambda x,y:['add',x,y];M=lambda x,y:['mul',x,y]
x=M(A(V(9),N(1)),A(M(['port','beta'],A(V(1),N(1))),N(1)));c=A(V(18),A(V(11),N(1)));mapping=[V(i) for i in range(16)]+[x]+[V(i) for i in range(16,22)]+[M(c,c)]+[V(i) for i in range(22,28)]+[M(V(27),V(27)),V(28)];assert len(mapping)==32
def sub(t):
 if t[0]=='var':return mapping[t[1]]
 if t[0] in ('num','port'):return t
 return [t[0],sub(t[1]),sub(t[2])]
a={r['gate']:r for r in old['residuals']};b={r['gate']:r for r in new['residuals']};assert len(a)==22 and len(b)==19 and set(a)-set(b)=={'X','c2','normalized_S2'}
for k in b:assert sub(a[k]['expr'])==b[k]['expr']
for k,i in [('X',16),('c2',23),('normalized_S2',30)]:
 t=a[k]['expr'];assert t[0:2]==['sub',V(i)] and sub(t[1])==sub(t[2])
s=(P/'SharingSeed28BridgeDraft.lean').read_text()
for name,expect in [('lift',[f'v {i}' for i in range(16)]+['(v 9 + 1) * (beta * (v 1 + 1) + 1)']+[f'v {i}' for i in range(16,22)]+['(v 18 + (v 11 + 1)) ^ 2']+[f'v {i}' for i in range(22,28)]+['(v 27) ^ 2','v 28']),('drop',[f'v {i}' for i in range(16)]+[f'v {i}' for i in range(17,23)]+[f'v {i}' for i in range(24,30)]+['v 31'])]:
 z=re.search(r'\bdef '+name+r'\b[^\n]*\n\s*!\[(.*?)\]',s,re.S);assert z and [t.strip() for t in z.group(1).split(',')]==expect
assert s.count('((p 0 : ℤ) : DiffRing V) = ι beta →')==2 and len(re.findall(r'^def (?:ForwardTarget|BackwardTarget)\b',s,re.M))==2 and not re.search(r'^(?:theorem|lemma)\b',s,re.M)
for text in ('InternalZero (SharingSeed28Sextic.seed p) v','InternalZero (SharingSeed31Sextic.seed p) (lift beta v)','InternalZero (SharingSeed31Sextic.seed p) v','InternalZero (SharingSeed28Sextic.seed p) (drop v)'):assert text in s
x=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],check=True,capture_output=True,timeout=30);assert not x.stderr and x.stdout==(P/'result.json').read_bytes();assert json.loads(x.stdout)['residuals']==19
print(json.dumps({'status':'PASS_SOURCE_ONLY','scope':'19 AST transfers, 3 removed rows, lift/drop positions and explicit beta cast; no Lean parsing or bridge theorem'},indent=2,sort_keys=True))
