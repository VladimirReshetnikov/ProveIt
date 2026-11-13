from pathlib import Path
from hashlib import sha256
from collections import Counter
import gzip,json,random,re
h=Path('research/trace73-center-probe'); parent=Path('con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json');candidate=h/'candidate.json';payload=Path('research/ten-positive-unshift-t-finite/coefficients')
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(parent)=='8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9' and sha(candidate)=='c83151606214c211993fa0c5b9913abae3b6bcf2b00af107e599e4855f936ca6'
g=json.loads(parent.read_text());c=json.loads(candidate.read_text());assert len(g['source'])==75 and len(c['source'])==73
assert [r for r in g['source'] if r[0] in ('LBt','center')]==[['LBt','*','V2','Bt'],['center','-','n','LBt']]
assert [[n,op,*['n' if x=='center' else x for x in (a,b)]] for n,op,a,b in g['source'] if n not in ('LBt','center')]==c['source']
for k in ['witnesses','fixed_numerals','coefficient_binding','output']:assert c[k]==g[k]
assert len(c['witnesses'])==10 and len(c['fixed_numerals'])==4 and Counter(x[1] for x in c['source'])=={'*':43,'+':17,'-':13}
nodes={};inputs=set(c['witnesses']+c['fixed_numerals']);degree={x:1 for x in c['witnesses']}|{x:0 for x in c['fixed_numerals']};avail=set(inputs)
for n,op,a,b in c['source']:
 assert n not in avail and op in ('+','-','*')
 for x in (a,b):assert (type(x) is int and x>=0) or x in avail
 da=0 if type(a)==int else degree[a];db=0 if type(b)==int else degree[b];degree[n]=da+db if op=='*' else max(da,db);avail.add(n);nodes[n]=(a,b)
assert degree[c['output']]==352
seen=set();todo=[c['output']]
while todo:
 x=todo.pop()
 if x in seen:continue
 seen.add(x)
 if x in nodes:todo.extend(z for z in nodes[x] if isinstance(z,str))
assert seen==inputs|nodes.keys()
prime=1000000007;env={n:{1:1} for n in c['witnesses']}
for n,info in c['coefficient_binding']['ports'].items():
 raw=gzip.decompress((payload/info['file']).read_bytes());assert sha256(raw).hexdigest()==info['raw_sha256'];env[n]={0:int.from_bytes(raw,'little')%prime}
def plus(x,y,sign):
 z=x.copy()
 for k,v in y.items():z[k]=(z.get(k,0)+sign*v)%prime
 return {k:v for k,v in z.items() if v}
def mul(x,y):
 z={}
 for i,a in x.items():
  for j,b in y.items():z[i+j]=(z.get(i+j,0)+a*b)%prime
 return {k:v for k,v in z.items() if v}
for n,op,a,b in c['source']:
 x={0:a%prime} if type(a)==int else env[a];y={0:b%prime} if type(b)==int else env[b];env[n]=mul(x,y) if op=='*' else plus(x,y,1 if op=='+' else -1)
poly=env[c['output']];assert max(poly)==352 and poly[352]==316589492
print('PASS external: 73 live operations (43 mul,17 add,13 sub), 10 witnesses/4 ports, exact parent row substitution, structural upper degree 352 and independent diagonal coefficient 316589492 modulo 1000000007; all raw payload hashes match.')
# Captured Lean evidence, not a Lean replay nor a JSON semantic theorem.
o=h/'observations/attempt02';r=json.loads((o/'terminal.json').read_text());assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(h/'run-v2.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='fe3d39ec315888286a4d9d5ec2763badf338dc11bf141c0e19fa58f575de1e5a'
for path,v in r['pins'].items():assert sha(path)==v['sha256'] and str(Path(path).resolve())==v['resolved']
for x in ('stdout','stderr'):assert sha(o/x)==r[x+'_sha256']
assert (o/'stdout').read_text().splitlines()==["'Trace73Center.centerZ_shift' depends on axioms: [propext]","'Trace73Center.substitution' depends on axioms: [propext]"] and not (o/'stderr').read_text()
src=(h/'Trace73CenterV2.lean').read_text();assert re.findall(r'^import\s+(\S+)',src,re.M)==['DiophantineConsistency.TenPositiveTrace75'] and not re.search(r'\b(sorry|admit)\b',src)
for text in ['[CommRing R]','Function.update v 7 (v 7+r.V*r.V*r.B)','value75 p (lift p v) = value73 p v','(regs p (lift p v)).Z = centerZ p v']:assert text in src
f=json.loads((h/'observations/attempt01/terminal.json').read_text());assert f['status']=='FAILED'
print('PASS Lean receipt/source: arbitrary commutative-ring 75→73 expression substitution with updated slot 7, direct selected parent object and retained [propext] reports; no independently replayed Lean or JSON binding.')
