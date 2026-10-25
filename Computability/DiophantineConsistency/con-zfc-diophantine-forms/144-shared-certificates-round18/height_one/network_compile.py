"""Cancel opposite source occurrences by one direct incidence edge."""
import sys,json,copy,random,math,argparse,time,hashlib
from pathlib import Path
from collections import defaultdict,Counter
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'upstream'));import contract
from normalize import normalize as original_normalize
BALANCE=True

def orient_rows(norm):
 """Greedily balance signs of identical monomials; exactness never uses optimality."""
 rowpol=[];balance=Counter()
 for row in norm["rows"]:
  d=Counter()
  for c,m in row["terms"]:d[tuple(sorted(m))]+=c
  rowpol.append(dict(d));balance.update(d)
 signs=[1]*len(rowpol)
 for sweep in range(20):
  changed=False
  for r,d in enumerate(rowpol):
   delta=sum(abs(balance[m]-2*signs[r]*c)-abs(balance[m]) for m,c in d.items())
   if delta<0:
    for m,c in d.items():balance[m]-=2*signs[r]*c
    signs[r]*=-1;changed=True
  if not changed:break
 for row,sign in zip(norm["rows"],signs):
  row["orientation"]=sign
  row["terms"]=[[sign*c,m] for c,m in row["terms"]]
 norm["sign_balance"]={"flipped_rows":sum(s<0 for s in signs),"l1_discrepancy":sum(abs(c) for c in balance.values())}
 return norm


def compile_graph(source,hubs,square_aliases=True):
 norm=contract.build.normalize(source)
 if BALANCE:norm=orient_rows(norm)
 vertices=[{'kind':'hub','index':i} for i in range(hubs)];blocks=[];occ=[];bymon=defaultdict(lambda:[[],[]])
 for r,row in enumerate(norm['rows']):
  block=list(range(len(vertices),len(vertices)+(len(row['terms'])+hubs-1)//hubs));blocks.append(block)
  vertices.extend({'kind':'row','row':r,'part':j} for j in range(len(block)))
  for j,(sign,m) in enumerate(row['terms']):
   item={'row':r,'occurrence':j,'sign':sign,'monomial':m,'vertex':block[j//hubs]};occ.append(item);bymon[tuple(sorted(m))][0 if sign>0 else 1].append(item)
 # Pair identical logical monomials of opposite sign across rows, without a
 # repeated vertex pair. Same-row occurrences cannot supply a source constraint.
 pairs=set();records=[];used=set()
 for mon,(pos,neg) in sorted(bymon.items(),key=lambda kv:(-min(map(len,kv[1])),len(kv[0]),kv[0])):
  for a in pos:
   for b in neg:
    ib=(b['row'],b['occurrence']);pa=tuple(sorted((a['vertex'],b['vertex'])))
    if ib in used or a['row']==b['row'] or pa in pairs:continue
    pairs.add(pa);used.add((a['row'],a['occurrence']));used.add(ib)
    records.append({'tail':a['vertex'],'head':b['vertex'],'sign':1,'monomial':list(mon),'bindings':[[a['row'],a['occurrence'],1],[b['row'],b['occurrence'],-1]]});break
 deg=[0]*hubs;offset=0
 for a in occ:
  if (a['row'],a['occurrence']) in used:continue
  options=[h for h in range(hubs) if (h,a['vertex']) not in pairs]
  h=min(options,key=lambda h:(deg[h],(h-offset)%hubs));offset=(h+1)%hubs;deg[h]+=1;pairs.add((h,a['vertex']))
  records.append({'tail':a['vertex'],'head':h,'sign':a['sign'],'monomial':a['monomial'],'bindings':[[a['row'],a['occurrence'],a['sign']]]})
 fake={'variables':norm['variables'],'rows':[{'terms':[[p['sign'],p['monomial']] for p in records]}]}
 flat,orientations=contract.build.orient(fake,True);variables=[];groups=defaultdict(list);products=[];edges=[]
 def fresh(kind,**kw):i=len(variables);variables.append({'kind':kind,**kw});return i
 common={}
 for v in sorted({b for a,b in orientations if b is not None and a!=b}):common[v]=fresh('shared',normalized_variable=v);groups[v].append(common[v])
 unit=fresh('unit_shared')
 for i,(rec,(a,b)) in enumerate(zip(records,orientations)):
  v=fresh('private',normalized_variable=a,row=rec['bindings'][0][0],occurrence=rec['bindings'][0][1]);other=v if a==b and a is not None else unit if b is None else common[b]
  p={'row':rec['bindings'][0][0],'occurrence':rec['bindings'][0][1],'sign':rec['sign'],'factors':[v,other],'logical_factors':[a,b],'bindings':rec['bindings']};products.append(p)
  edges.append({'kind':'prescribed','tail':rec['tail'],'head':rec['head'],'coefficient':rec['sign'],'monomial':p['factors'],'product':i})
 for r,block in enumerate(blocks):
  for left,right in zip(block,block[1:]):
   w=fresh('flow',component='row',row=r,edge=len(edges));edges.append({'kind':'free','tail':left,'head':right,'coefficient':1,'monomial':[w]})
 for h in range(hubs-1):
  w=fresh('flow',component='hub',edge=len(edges));edges.append({'kind':'free','tail':h,'head':h+1,'coefficient':1,'monomial':[w]})
 cert={'normalization':norm,'products':products,'vertices':vertices,'edges':edges,'row_blocks':blocks,'hub_vertices':list(range(hubs)),'equality_cycles':[],'unit_path':[],'network_pairing':{'source_occurrences':len(occ),'paired_edges':sum(len(p['bindings'])==2 for p in products),'unpaired_edges':sum(len(p['bindings'])==1 for p in products)}}
 initial={'variables':variables,'terms':[]};p=contract.energy(cert)
 if any(abs(c)!=1 for c in p.values()):raise ValueError('Initial network energy height')
 return initial,cert

def run(source,hubs=16,seed=0):
 contract.build.compile_graph=compile_graph
 contract.build.normalize=original_normalize
 a,c=contract.contract(source,hubs,seed,3);a['schema']='network-height-one-quartic-v1';c['schema']='network-height-one-certificate-v1';a['metrics'].update(c['network_pairing']);return a,c

def main():
 p=argparse.ArgumentParser();p.add_argument('--source',type=Path);p.add_argument('--source-id',default='263');p.add_argument('--out',type=Path);p.add_argument('--hubs',type=int,nargs='+',default=[16,24,32,48,64,128,192]);p.add_argument('--seeds',type=int,nargs='+',default=[0]);args=p.parse_args();sp=args.source or HERE/'sources'/('refactored'+args.source_id)/'source.json';raw=sp.read_bytes();source=json.loads(raw)
 for h in args.hubs:
  for seed in args.seeds:
   t=time.time();a,c=run(source,h,seed);c['source_sha256']=hashlib.sha256(raw).hexdigest();print(json.dumps({'hubs':h,'seed':seed,'metrics':a['metrics'],'seconds':round(time.time()-t,2)}),flush=True)
   if args.out:
    out=args.out/f'h{h}_s{seed}';contract.write(out/'polynomial.json',a);contract.write(out/'certificate.json',c);contract.write(out/'metrics.json',a['metrics'])
if __name__=='__main__':main()
