import sys,json,itertools,hashlib
from pathlib import Path
from functools import cache
import argparse
HERE=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
sys.path.insert(0,str(HERE/'vendor'))
import source_language as s, build221 as b, source_splice as sp
base=HERE/'baseline'; rows=json.loads((base/'sites215.json').read_text());root=s.tree(rows)
T=b.read_table((base/'k215.native.tm').read_bytes());groups,paths=b.decoder_map(T,root)
macros={'a':b.sole(groups,98),'b':b.sole(groups,12),'c':b.sole(groups,166),'I':b.sole(groups,90)}
inc=('CI',1);macros.update(R=(macros['I'],inc),Q=(macros['I'],(inc,inc)),E=(macros['I'],((inc,inc),inc)),F=(macros['a'][0],inc))
flat=lambda x: tuple(tuple(r[1:])for r in s.sites(x))
nodes=sp.nodes(root)
words={n:flat(n)for n in nodes if s.boundary(n)==(0,0,False)}
contracts=json.loads((base/'native_axiom_contracts.json').read_text())
variants={}
for row in contracts['rows']:
 if row['name']=='rho8':continue
 w=row['postfix'];rg=tuple(row['span']);assert flat(sp.serial(sp.closed_forest(root,*rg)))==sum((flat(macros[t])for t in w),())
 if row['name'] in ('rho2','rho3','rho5','growG'):
  ast=row['expression_AST'];assert ast[0]=='I' and ast[2][0]=='I';new=['I',ast[2][1],['I',ast[1],ast[2][2]]]
  def postfix(a):
   if isinstance(a,str):return a.lower()if a in ('A','B','C')else a
   return postfix(a[1])+postfix(a[2])+a[0]
  variants[row['name']]=(rg,postfix(new))
variants['rho6dual']=((888,1171),'caacFIQFIQI')

def best_tree(word,base_nodes,limit=8):
 # Exact minimum novel-node count beam over closed blocks; never slice open loops.
 ww=sum((flat(macros[t])for t in word),());N=len(ww)
 tokens={}
 for n,w in words.items():
  L=len(w)
  for i in range(N-L+1):
   if ww[i:i+L]==w:tokens.setdefault((i,i+L),[]).append(n)
 # Closed primitives CI are acceptable; all other leaves occur only inside closed blocks.
 forward={0};backward={N}
 for i in range(N+1):
  if i in forward:forward.update(j for a,j in tokens if a==i)
 for j in range(N,-1,-1):
  if j in backward:backward.update(i for i,b in tokens if b==j)
 boundaries=sorted(forward & backward)
 print('DP boundaries',len(boundaries),'primitive length',N,flush=True)
 reach={}
 for n in base_nodes:reach[n]=frozenset()
 @cache
 def newnodes(n):
  if n in base_nodes:return frozenset()
  return frozenset([n])if s.leaf(n)else frozenset([n])|newnodes(n[0])|newnodes(n[1])
 @cache
 def shape(n):
  if s.leaf(n):return 0,0,0
  ld,lz,ll=shape(n[0]);rd,rz,rl=shape(n[1]);return max(ld,rd)+1,max(lz,rz,ll+1),ll+1
 dp={}
 for L in range(1,len(boundaries)):
  for start in range(len(boundaries)-L):
   i,j=boundaries[start],boundaries[start+L];candidates={n:newnodes(n)for n in tokens.get((i,j),())}
   for k in boundaries[start+1:start+L]:
    if (i,k)not in dp or (k,j)not in dp:continue
    for a,an in dp[i,k]:
     for c,cn in dp[k,j]:
      n=(a,c);candidates[n]=an|cn|({n}if n not in base_nodes else set())
   if candidates:dp[i,j]=sorted(candidates.items(),key=lambda x:(len(x[1]),shape(x[0])[1],shape(x[0])[0]))[:limit]
 return dp[0,N]

out=args.output;out.mkdir(exist_ok=False)
result=[]
for name,(rg,w)in variants.items():
 # Remove original row first to compute true retained node set.
 outside=sp.apply_closed_splices(root,{rg:None}); bn=sp.nodes(outside)
 opts=best_tree(w,bn,4)
 entry=[]
 for k,(n,new)in enumerate(opts):
  nr=sp.apply_closed_splices(root,{rg:n});rr=s.sites(nr);g=sp.cfg_intervals(rr);assert g==sp.cfg_arithmetic(rr)
  oldg=sp.cfg_intervals(rows)
  assert len(rr)==len(rows) and all(g[i]==oldg[i] for i in range(len(rr)) if not rg[0]<=i<rg[1])
  p=out/f'{name}-{k}.json';p.write_bytes(s.compact(rr));m=s.metrics(nr)
  entry.append({'file':str(p),'metrics':m,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
 print(name,w,entry,flush=True);result.append({'name':name,'postfix':w,'span':rg,'options':entry})
(out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
