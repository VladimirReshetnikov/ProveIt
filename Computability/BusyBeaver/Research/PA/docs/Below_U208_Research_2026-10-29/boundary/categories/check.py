"""Independent certificate checker: arithmetic CFG, representative abstract transfer.
No generator or interval resolver is imported. Checks remain active with -O.
"""
from pathlib import Path
import argparse,json,hashlib

def need(c,m):
 if not c:raise ValueError(m)
def graph(rows):
 leaves={p:i for i,(p,op,a)in enumerate(rows)};need(len(leaves)==len(rows),'duplicate leaf');depth=max(map(len,leaves))
 prefixes={p[:j]for p in leaves for j in range(len(p))};need(all(p and set(p)<={'0','1'}for p in leaves),'binary paths');need(not(set(leaves)&prefixes),'prefix overlap');need(all(p+b in prefixes or p+b in leaves for p in prefixes for b in'01'),'full tree');need(sorted(leaves)==[r[0]for r in rows],'ordinal order')
 def locate(p):
  bits=p+'0'*depth
  for k in range(1,depth+1):
   if bits[:k]in leaves:
    need('1'not in p[k:],'stray suffix');return leaves[bits[:k]]
  raise ValueError('missing leaf')
 def inc(p):return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b')if p else''
 def cut(p,e,n):
  positions=[j for j,b in enumerate(p)if b==e];return p[:positions[-n]]if len(positions)>=n else''
 g=[]
 for p,op,a in rows:
  need(op in('CI','CD','CB','CC','CH'),'opcode')
  if op in('CI','CD'):need(type(a)is int and 0<=a<9,'register')
  if op in('CB','CC'):need(type(a)is int and a>=1,'depth')
  g.append([locate(inc(p))]if op=='CI'else[locate(inc(cut(p,'0',1))),locate(inc(p))]if op=='CD'else[locate(inc(cut(p,'0',a)))]if op=='CB'else[locate(cut(p,'1',a))]if op=='CC'else[])
 need(locate('')==0,'root');return g

def verify(raw,cert,other=None):
 rows=json.loads(raw);g=graph(rows);states=cert['states'];need(len(rows)==len(states)==3909,'count');need(hashlib.sha256(raw).hexdigest()==cert['source_sha256'],'source hash');need(g==cert['graph'],'CFG');need(cert['seed_ordinal']==136 and cert['seed_registers']==[1,0,13,0,0,1,0,0,1],'seed metadata')
 for s in states:
  need(s is None or(len(s)==9 and all(type(m)is int and 0<m<16 for m in s)),'mask shape')
 need(states[136]is not None,'seed missing')
 for r,v in enumerate(cert['seed_registers']):need(states[136][r]&(1<<min(v,3)),'seed inclusion')
 edges=0
 # Representatives3 and4 cover distinct decrement images of the >=3 category.
 reps={0:[0],1:[1],2:[2],3:[3,4]}
 for i,(p,op,arg)in enumerate(rows):
  s=states[i]
  if s is None:continue
  images={}
  if op in('CI','CD'):
   for c,values in reps.items():
    if not(s[arg]>>c&1):continue
    for v in values:
     branch=0 if op=='CI'else int(v>0);value=v+1 if op=='CI'else max(v-1,0)
     images[branch]=images.get(branch,0)|(1<<min(value,3))
  else:images={j:None for j in range(len(g[i]))}
  for branch,mask in images.items():
   dest=g[i][branch];t=states[dest];need(t is not None,'successor missing')
   for r,m in enumerate(s):need(((mask if r==arg and op in('CI','CD')else m)&~t[r])==0,'successor mask inclusion')
   edges+=1
 dead=[i for i,s in enumerate(states)if s is None];zeros=[i for i,(_,op,r)in enumerate(rows)if op=='CD'and states[i]is not None and states[i][r]==1]
 need(dead==[3848,3849,3892]and zeros==[3847,3891],'claimed guards')
 if other is not None:
  otherrows=json.loads(other);need([x[1:]for x in otherrows]==[x[1:]for x in rows],'other word');need(graph(otherrows)==g,'other CFG')
 return {'status':'INDEPENDENT_INVARIANT_PASS','admitted_sites':3909-len(dead),'checked_edges':edges,'unreachable_sites':dead,'always_zero_decrements':[[i,rows[i][1],rows[i][2]]for i in zeros],'other_source_transported':other is not None,'scope':'Inductive product overapproximation from calibrated source entry; not all admitted valuations are reachable. Ordinary PA-formalizable invariant, not a new kernel certificate.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('certificate',type=Path);p.add_argument('--other',type=Path);a=p.parse_args();print(json.dumps(verify(a.source.read_bytes(),json.loads(a.certificate.read_text()),a.other.read_bytes()if a.other else None),indent=2))
