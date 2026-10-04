#!/usr/bin/env python3
"""Fresh independent full-array and actual-hat review of U21 prime recentering."""
import argparse,hashlib,json
from pathlib import Path
from collections import Counter,deque
AUTHOR={
 'residue_affine_sparse_prime_recenter.py':'c5d8b2690f1e2a9b50aa063a95f81297ff388b276ab83ce487aa4cbaacc46798',
 'residue_affine_sparse_prime_recenter.json':'e35399b892850ace2bf860fd37f0e3e9f8af34dd8e516f66718547e0689fe26c',
 'residue_affine_sparse_prime_recenter.md':'78e81a12145ecf2b5b57fecdbef614cafa2a96ff0b86e488c4479546914c108c'}
PINS={
 'residue_affine_sparse_joint_recoding.py':'386f00228dd250a1c582a3bf93724e9732db71cdd8d4fea6828d0b78d06fe443',
 'residue_affine_sparse_joint_recoding.json':'a3b00883d84e7c8e9a6aea04ec3e54776fe927f7193f60a04050246f32039284',
 'residue_affine_sparse_joint_recoding.md':'16d4a9e60343eb4f8f4ee78e8d60e7aeb2ee73b8d045241dd4951e124cf7b404',
 'residue_affine_sparse_factored.json':'39e52871ae5137f8edd111055e6338db4bf17b232d145a24390b1675d8c99fda'}
CODES=[0,1,15,21,9,17,13,11,5,18,8,38,30,32,10,3,12,4,40,2,6,7,14]
OUT='norm_output';U='sparse_all_units';B='radix_86';P='scale_89';PREFIX='recentered_current_prefix'
def ck(v,s):
 if not v:raise ValueError(s)
def sha(v):return hashlib.sha256(v).hexdigest()
def enc(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def obj(xs):
  out={}
  for k,v in xs:ck(k not in out,'duplicate key');out[k]=v
  return out
 def bad(x):raise ValueError('noninteger JSON '+x)
 return json.loads(p.read_text(),object_pairs_hook=obj,parse_float=bad,parse_constant=bad)
def table(rows):
 out={}
 for r in rows:
  ck(type(r)is list and len(r)==4,'row length');n,o,a,b=r
  ck(type(n)is str and n not in out and o in ['+','-','*'],'SSA/op')
  ck(all(type(x)in [int,str] for x in [a,b]),'operand type');out[n]=(o,a,b)
 return out
def closure(d,roots):
 seen=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is str and n in d and n not in seen:seen.add(n);todo+=list(d[n][1:])
 return seen
def graph(rows,free):
 d=table(rows);known=set(free);deps={};users={n:[] for n in d}
 for n,o,a,b in rows:
  ck(n not in known and all(type(x)is int or x in known for x in [a,b]),'literal topological order')
  known.add(n);deps[n]={x for x in [a,b] if x in d}
  for x in deps[n]:users[x].append(n)
 queue=deque(n for n in d if not deps[n]);number=0
 while queue:
  n=queue.popleft();number+=1
  for u in users[n]:
   deps[u].remove(n)
   if not deps[u]:queue.append(u)
 ck(number==len(d),'independent Kahn check')
 ck(closure(d,[OUT])==set(d),'all rows live')
 used={x for r in rows for x in r[2:] if type(x)is str and x not in d}
 ck(used==set(free),'exact supplied ports live')
 c=Counter(r[1] for r in rows)
 return dict(total=len(rows),M=c['*'],A=c['+']+c['-'])
def add(a,b,s=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+s*c
 return {m:c for m,c in out.items() if c}
def mul(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   z=tuple(sorted(m+n));out[z]=out.get(z,0)+c*d
 return {m:c for m,c in out.items() if c}
def expand(d,target,cuts):
 memo={n:{(n,):1} for n in cuts}
 def at(n):
  if type(n)is int:return {():n} if n else {}
  if n not in memo:
   ck(n in d,'uncut supplied value '+n);o,a,b=d[n];a,b=at(a),at(b)
   memo[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
  return memo[n]
 return at(target)
def serial(p):return [[list(k),v] for k,v in sorted(p.items())]
def affine(rows):
 z=(0,)*37;v={f'edge{i}_hat':tuple(int(j==i+1) for j in range(37)) for i in range(36)}
 for n,o,a,b in rows:
  aa=(a,)+z[1:] if type(a)is int else v.get(a)
  bb=(b,)+z[1:] if type(b)is int else v.get(b)
  if aa is None or bb is None:continue
  if o in ['+','-']:v[n]=tuple(x+(y if o=='+' else -y) for x,y in zip(aa,bb))
  elif not any(aa[1:]):v[n]=tuple(aa[0]*x for x in bb)
  elif not any(bb[1:]):v[n]=tuple(bb[0]*x for x in aa)
 return v

def degree(rows,free):
 raw={n:1 for n in free}
 for n,o,a,b in rows:
  x,y=[0 if type(v)is int else raw[v] for v in [a,b]];raw[n]=x+y if o=='*' else max(x,y)
 names=['native__wn2','native__R12','native__R10a','native__gam'];X,a,c,G=names
 actual=expand(table(rows),'native__R15',set(names))
 expect={tuple(sorted(m)):k for m,k in [([X,X],1),([a,c,X],2),([G,X],2),([a,c,G],2),([G,G],1),([a,c,c],-4),([c,c],-3)]}
 ck(actual==expect,'guarded seven-term main norm')
 weights={n:raw[n] for n in names};bound=max(sum(weights[n] for n in m) for m in actual)
 fresh={n:1 for n in free}
 for n,o,a,b in rows:
  x,y=[0 if type(v)is int else fresh[v] for v in [a,b]];fresh[n]=x+y if o=='*' else max(x,y)
  if n=='native__R15':fresh[n]=bound
 return dict(naive=raw[OUT],guarded=fresh[OUT],main=bound,weights=weights,control=fresh['norm_residual1'],
  unit=fresh[U],SOS=fresh['norm_sum5'],main_norm_coefficients=serial(actual))

def identical_values(old,new,free):
 # Independent 37-entry hat/constant normal form; every other input stays
 # a distinct symbolic port. The Q or native values are never freed cuts.
 pool={}
 def intern(t):
  if t not in pool:pool[t]=len(pool)
  return pool[t]
 def run(rows):
  av=affine(rows);ids={n:intern(('port',n)) for n in free}
  for i in range(36):ids[f'edge{i}_hat']=intern(('hat-affine',tuple(int(j==i+1) for j in range(37))))
  for n,o,a,b in rows:
   aa=intern(('hat-affine',(a,)+(0,)*36)) if type(a)is int else ids[a]
   bb=intern(('hat-affine',(b,)+(0,)*36)) if type(b)is int else ids[b]
   ids[n]=intern(('hat-affine',av[n])) if n in av else intern((o,aa,bb))
  return ids,av
 a,av=run(old);b,bv=run(new)
 common=set(table(old))&set(table(new));exceptions=sorted(n for n in common if a[n]!=b[n])
 ck(exceptions==sorted(['joint_8','joint_18','joint_19','joint_20','joint_21']),'exact five changed retained values')
 for n in exceptions:
  delta=tuple(y-x for x,y in zip(av[n],bv[n]))
  want=av['prime_selector_111' if n=='joint_21' else 'prime_selector_113']
  ck(delta==want,'exact changed affine value '+n)
 ck(a['joint_21']==b[PREFIX],'restored prefix all-ring identity')
 ck(a[OUT]==b[OUT],'entire bound-DAG identity')
 for n in [U,B,P]+['norm_residual'+str(i) for i in range(6)]:ck(a[n]==b[n],'actual computed boundary '+n)
 return a,b,av,bv,exceptions

def build(root,author_root):
 for base,pins in [(root,PINS),(author_root,AUTHOR)]:
  for n,h in pins.items():ck(sha((base/n).read_bytes())==h,'pin '+n)
 parent=read(root/'residue_affine_sparse_joint_recoding.json');child=read(author_root/'residue_affine_sparse_prime_recenter.json')
 fact=read(root/'residue_affine_sparse_factored.json');snapshot=enc(parent)
 ck(parent['source_sha256']==PINS['residue_affine_sparse_joint_recoding.py'],'parent helper binding')
 ck(child['source_sha256']==AUTHOR['residue_affine_sparse_prime_recenter.py'],'author helper binding')
 ck(len(child['packets'])==len(parent['packets'])==2,'two complete interfaces')
 edges=[[0,0,'I',2,1,2,1,2],[0,1,'I',2,1,2,1,2]]
 for q,inst in enumerate(fact['default_table'],1):
  op,reg,*targets=inst;prime=fact['default_primes'][reg];targets=[t+1 for t in targets]
  if op=='I':edges.append([q,targets[0],op,prime,1,prime,1,prime])
  else:
   ck(op in ['D','T'],'actual U21 opcode')
   edges.append([q,targets[0],op,prime,prime,1,prime,1] if op=='D' else [q,targets[0],op,prime,prime,prime,prime,prime])
   edges.append([q,targets[1],'Z',prime,prime,prime,1,1])
 ck(len(edges)==36 and edges==fact['edges']==parent['literal_edges']==child['literal_edges'],'actual full 36-edge table')
 ck(parent['new_codes']==child['state_codes']==CODES,'same literal23 codes')
 ck(len(set(CODES))==23 and max(CODES)==40 and CODES[0]==0 and CODES[-1]==14,'code injectivity/loader/halt')
 # Check the changed weight/correction description independently against U21.
 weights={2:0,3:1,5:2,7:3,11:8,13:9,17:18,19:11};correction={3:-1,5:-1,11:29,12:21,13:32,14:1,18:32}
 fresh_codes=[0]+[weights[fact['default_primes'][row[1]]]+4*(row[0]=='I')+correction.get(q,0) for q,row in enumerate(fact['default_table'],1)]+[14]
 ck(fresh_codes==CODES,'recentered weights retain all codes')
 results=[]
 for j,(old_item,new_item) in enumerate(zip(parent['packets'],child['packets'])):
  old,new=old_item['packet'],new_item['packet'];od,nd=table(old['source']),table(new['source'])
  ck(old_item['interface']==new_item['interface']==['one_program','two_program'][j],'interface ordering')
  ck(sha(enc(old['source']))==old['source_sha256'] and sha(enc(new['source']))==new['source_sha256'],'both complete array bindings')
  unchanged_fields=set(old)-{'source','source_sha256','ledger','certificate_ledger'}
  ck(set(new)==set(old) and all(enc(new[k])==enc(old[k]) for k in unchanged_fields),'every interface/recipe/degree field literal')
  guards={'joint_8':('*',17,'prime_selector_113'),'joint_1':('+','edge_14','control_codes__duplicate_state_8'),
   'joint_2':('+','joint_1','edge_15'),'joint_21':('+','joint_20','joint_2'),'joint_22':('+','joint_21','joint_11')}
  ck(all(od[n]==r for n,r in guards.items()),'literal immediate-parent edit guards')
  users={n:sorted(r[0] for r in old['source'] if n in r[2:]) for n in ['joint_1','joint_2','joint_21']}
  ck(users=={'joint_1':['joint_2'],'joint_2':['joint_21'],'joint_21':['joint_22']},'private original producers')
  expected=dict(od);del expected['joint_1'];del expected['joint_2']
  expected['joint_8']=('*',18,'prime_selector_113')
  expected['joint_21']=('+','joint_20','control_codes__duplicate_state_8')
  expected[PREFIX]=('-','joint_21','prime_selector_111')
  expected['joint_22']=('+',PREFIX,'joint_11')
  ck(expected==nd,'entire independently reconstructed definition table')
  ck(set(od)-set(nd)=={'joint_1','joint_2'} and set(nd)-set(od)=={PREFIX},'exact two deletions one addition')
  free=new['parameters']+new['witnesses'];ck(len(new['witnesses'])==67 and len(free)==69+j,'all supplied port counts')
  go,gn=graph(old['source'],free),graph(new['source'],free)
  ck(go==dict(total=467-j,M=171,A=296-j) and gn==dict(total=466-j,M=171,A=295-j),'complete 1A saving')
  ck(new['ledger']==dict(operations=466-j,multiplications=171,additions_subtractions=295-j,witnesses=67),'declared complete ledger')
  base=closure(od,[U]+['norm_residual'+str(i) for i in [0,2,3,4,5]])
  ck(len(base)==389-j and all(od[n]==nd[n] for n in base),'full noncontrol base literal')
  native={n for n in od if n.startswith('native__')};finals={n for n in od if n.startswith('norm_')}
  ck(len(native)==72 and all(od[n]==nd[n] for n in native),'literal72 native rows')
  ck(len(finals)==20 and all(od[n]==nd[n] for n in finals),'literal20 comparisons/finalizer rows')
  ck(len(finals-base)==15,'remaining15 finalizer rows')
  a,b,av,bv,exceptions=identical_values(old['source'],new['source'],free)
  def support(ids):return (-len(ids),)+tuple(int(i in ids) for i in range(36))
  for i in range(36):ck(od[f'edge_{i}']==nd[f'edge_{i}']==('-','edge'+str(i)+'_hat',1),'actual raw selector binding')
  ck(av['prime_selector_113']==bv['prime_selector_113']==support([5,8,9,14,15]),'paid G17 support and constant')
  ck(av['prime_selector_111']==bv['prime_selector_111']==support([5,8,9]),'paid A3 support and constant')
  ck(av['control_codes__duplicate_state_8']==support([24,25]),'paid D14 support')
  ck(tuple(x-y for x,y in zip(av['prime_selector_113'],av['prime_selector_111']))==support([14,15]),'actual hats G17-A3=D9')
  ck({'prime_selector_111','prime_selector_113','control_codes__duplicate_state_8'}<=base,'all donors already paid in retained base')
  words=[]
  for env,label in [(av,'parent'),(bv,'child')]:
   for key,edgecol in [('current',0),('following',1)]:
    name=new['control_interfaces'][key];v=tuple(CODES[e[edgecol]] for e in edges)
    ck(env[name]==(-sum(v),)+v,'entire actual36 hat word')
    words.append(dict(source=label,kind=key,name=name,affine_coefficients=list(env[name])))
  def word_cost(d):
   c=closure(d,['joint_24'])-base;t=closure(d,['joint_61'])-base
   def cost(xs):
    v=Counter(d[n][0] for n in xs);return [len(xs),v['*'],v['+']+v['-']]
   return dict(current=cost(c),target=cost(t),union=cost(c|t),shared=sorted(c&t))
  costs=[word_cost(od),word_cost(nd)]
  ck(costs==[dict(current=[24,9,15],target=[37,12,25],union=[60,20,40],shared=['joint_12']),
             dict(current=[23,9,14],target=[37,12,25],union=[59,20,39],shared=['joint_12'])],'full joint word union accounting')
  private=set(nd)-base-(finals-base);cc=Counter(nd[n][0] for n in private)
  ck((len(private),cc['*'],cc['+']+cc['-'])==(62,22,40),'paid private control62')
  c=Counter(nd[n][0] for n in set(nd)-finals)
  ck(new['certificate_ledger']==dict(operations=446-j,multiplications=164,additions_subtractions=282-j,equations=7,witnesses=67),'certificate ledger')
  ck((len(nd)-len(finals),c['*'],c['+']+c['-'])==(446-j,164,282-j),'derived certificate ledger')
  cuts={f'edge{i}_hat' for i in range(36)}|{B,P,U}|{f'norm_residual{i}' for i in [0,2,3,4,5]}
  oldF=expand(od,OUT,cuts);newF=expand(nd,OUT,cuts)
  ck(oldF==newF,'full actual-hat output expansion identity')
  # Bound cuts were proved equal in the full DAG; this is supplementary expansion.
  final=expand(nd,OUT,{U}|{f'norm_residual{i}' for i in range(6)})
  want={():-1,(U,):1}
  for i in range(6):want[tuple(sorted([U,f'norm_residual{i}',f'norm_residual{i}']))]=1
  ck(final==want,'actual entire native times SOS finalizer')
  deg=degree(new['source'],free)
  ck((deg['guarded'],deg['naive'],deg['main'],deg['unit'],deg['SOS'],deg['control'])==[(5091,5157,816,4993,98,2),(5160,5227,827,5062,98,3)][j],'fresh guarded whole degree')
  heights=[['height_83','+','program','input'],['height_85','+','height_83','height_slack'],['radix_86','*',64,'height_85']] if j==0 else [['height_85','+','input','height_slack'],['radix_86','*','radix_program','height_85']]
  ck(new['literal_height_radix_rows']==heights and all(nd[n]==(o,x,y) for n,o,x,y in heights),'actual original height/radix recipe')
  results.append(dict(interface=new_item['interface'],ledger=gn,private_consumers=users,base_rows=len(base),native_rows=72,
   comparison_finalizer_rows=20,private_control_rows=62,word_costs=costs,actual_hat_words=words,
   donor_supports={n:list(av[n]) for n in ['prime_selector_111','prime_selector_113','control_codes__duplicate_state_8']},
   retained_value_exceptions=exceptions,identical_retained_computed_values=len(set(od)&set(nd))-len(exceptions),
   restored_prefix=[PREFIX,'joint_21'],full_actual_hat_output_terms=len(newF),full_actual_hat_output=serial(newF),
   formal_finalizer=serial(final),degree=deg,height_rows=heights))
 ck(enc(parent)==snapshot,'parent byte data remains immutable')
 return dict(status='PASS_INDEPENDENT_U21_PRIME_RECENTER',source_sha256=sha(Path(__file__).read_bytes()),
  author_pins=AUTHOR,parent_pins=PINS,edges=edges,codes=CODES,results=results,total_rows=sum(r['ledger']['total'] for r in results),
  scope=dict(all_ring_output_identity=True,same_positive_coordinates='within each own parent fixed recipe',
   exact_degree_claim=False,cross_interface_positive_map=False,author_or_predecessor_execution=False,
   full_sources_reconstructed=True,new_native_or_history_fixtures=False))

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();r=build(a.root,a.author_root)
 if a.output:
  with a.output.open('x') as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(enc(r)==enc(read(a.expect)),'exact typed review receipt')
 print(r['status'],[x['ledger']['total'] for x in r['results']],r['total_rows'],'rows')
if __name__=='__main__':main()
