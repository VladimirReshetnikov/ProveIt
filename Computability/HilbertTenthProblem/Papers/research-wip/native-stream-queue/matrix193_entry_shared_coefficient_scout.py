#!/usr/bin/env python3
"""Fresh entry-sharing component compiler; predecessor JSON is inert data."""
import json,hashlib,argparse,random,copy
from math import gcd
from pathlib import Path
from collections import Counter
PINS={
'matrix193_composed_output_scout.py':'e8b2982bdf00a9be6e6e80a1b86c38f3536a5345c60adf3103e8f7356ed01317',
'matrix193_composed_output_scout.json':'a231b3ef66f0ab0f729bf50e40f87fad5a5d784e089249dbb4e93e11696a9e37',
'matrix193_composed_output_scout.md':'83711eab17b18f38c2bd47ddd3d803fde5adf339f7b5bbc0be2839a3bfeff748',
'matrix193_structured_coefficient_scout.py':'39ab5c942af5bd6d725d2c17e89d2222e3e44bf26cc59e3c1bad1d4e011e10a9',
'matrix193_structured_coefficient_scout.md':'8e49bed183eed196768951d3a86febc6cbd8d0a2e8898387c41b3b0e0ebeced3',
'matrix193_gamma1_recode.json':'9cdd0274625c847aa77f5907ba6554ee16f37895f5c026b3d776595330676668',
'matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742'}
def ck(v,m):
 if not v:raise ValueError(m)
def mm(a,b):return [a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3]]
def inv(a):
 ck(a[0]*a[3]-a[1]*a[2]==1,'det1');return [a[3],-a[1],-a[2],a[0]]
def word(w,letters):
 a=[1,0,0,1]
 for x in w:a=mm(a,letters[x])
 return a

def trim(a):
 a=list(a)
 while a and a[-1]==0:a.pop()
 return tuple(a)
def pa(a,b,sgn=1):return trim([(a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def pm(a,b):
 if not a or not b:return ()
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]+=x*y
 return trim(z)
class DAG:
 def __init__(self,Q,rows):
  self.Q=Q;self.rows=[];self.cache={};self.values={Q:(0,1)};self.known={():0,(1,):1,(0,1):Q};self.powers={0:1,1:Q}
  for n,op,l,r in rows:
   if n==Q:continue
   if (type(l)is int or l in self.values) and (type(r)is int or r in self.values):
    a=self.val(l);b=self.val(r);v=pm(a,b) if op=='*' else pa(a,b,1 if op=='+' else -1);self.values[n]=v;self.known.setdefault(v,n)
    if v and v[-1]==1 and all(t==0 for t in v[:-1]):self.powers.setdefault(len(v)-1,n)
   self.cache[(op,l,r)]=n
  self.affine={};self.affine_hits=[];self.trace_records=[]
  for n,v in self.values.items():self.index_affine(n,v)
 def affine_key(self,v):
  if len(v)<2:return None
  g=0
  for a in v[1:]:g=gcd(g,abs(a))
  if v[-1]<0:g=-g
  return tuple(a//g for a in v[1:]),g,v[0]
 def index_affine(self,n,v):
  z=self.affine_key(v)
  if z:self.affine.setdefault(z[0],[]).append((n,z[1],z[2]))
 def raw(self,op,a,b,v):
  if v in self.known:return self.known[v]
  n='cp'+str(len(self.rows));self.rows.append([n,op,a,b]);self.values[n]=v;self.known[v]=n;self.index_affine(n,v);return n
 def val(self,x):return trim([x]) if type(x)is int else self.values[x]
 def op(self,op,a,b):
  if type(a)is int and type(b)is int:return a*b if op=='*' else a+b if op=='+' else a-b
  if op=='*' and (a==0 or b==0):return 0
  if op=='*' and a==1:return b
  if op=='*' and b==1:return a
  if op in ['+','-'] and b==0:return a
  if op=='+' and a==0:return b
  v=pm(self.val(a),self.val(b)) if op=='*' else pa(self.val(a),self.val(b),1 if op=='+' else -1)
  if v in self.known:return self.known[v]
  z=self.affine_key(v)
  if z:
   choices=[]
   for old,scale,const in self.affine.get(z[0],[]):
    if z[1]%scale:continue
    ratio=z[1]//scale;off=z[2]-ratio*const;cost=1 if abs(ratio)==1 or off==0 else 2
    choices.append((cost,old,ratio,off))
   if choices:
    cost,old,ratio,off=min(choices)
    if cost<=2:
     self.affine_hits.append({'target':list(v),'source':old,'scale':ratio,'offset':off})
     if ratio==1:return self.raw('+',old,off,v)
     if ratio==-1:return self.raw('-',off,old,v)
     scaled=tuple(ratio*x for x in self.val(old));tmp=self.raw('*',ratio,old,scaled)
     return self.raw('+',tmp,off,v) if off else tmp
  return self.raw(op,a,b,v)
 def add(self,a,b):return self.op('+',a,b)
 def sub(self,a,b):return self.op('-',a,b)
 def mul(self,a,b):return self.op('*',a,b)
 def sum(self,xs):
  r=0
  for x in xs:r=self.add(r,x)
  return r
 def pow(self,k):
  if k not in self.powers:
   v=self.mul(self.pow(k//2),self.pow(k//2));self.powers[k]=self.mul(v,self.Q) if k%2 else v
  return self.powers[k]
 def poly(self,co,step=1):
  at=None;v=0
  for i in reversed(range(len(co))):
   if co[i]==0:continue
   v=co[i] if at is None else self.add(self.mul(v,self.pow(step*(at-i))),co[i]);at=i
  return 0 if at is None else self.mul(v,self.pow(step*at))
 def rep2(self,n):
  co=tuple(1 if j%2==0 else 0 for j in range(2*n-1))
  if co in self.known:return self.known[co]
  nxt=co+(0,1)
  if nxt in self.known:return self.sub(self.known[nxt],self.pow(2*n))
  h=n//2;v=self.mul(self.rep2(h),self.add(self.pow(2*h),1))
  return self.add(v,self.pow(4*h)) if n%2 else v
 def mask_poly(self,indices,step):
  e=set(indices);power=lambda j:self.pow(step*j)
  if e=={0,6,8,25,27}:return self.add(self.mul(self.add(power(6),power(25)),self.add(power(2),1)),1)
  if e=={13,15,17,21,23}:return self.mul(power(13),self.add(self.mul(self.add(power(2),1),self.add(power(8),power(2))),1))
  if e=={8,9,11,12,14,15}:return self.mul(power(8),self.mul(self.add(1,power(1)),self.sum([1,power(3),power(6)])))
  if e=={2,3,13,16,17,18}:return self.add(self.mul(power(2),self.mul(self.add(1,power(1)),self.add(1,power(14)))),self.mul(power(13),self.add(1,power(5))))
  return self.poly([int(j in e) for j in range(max(e)+1)],step)
 def matrix_poly(self,ms,step=1):
  nonzero=[j for j,a in enumerate(ms) if any(a)]
  if len(nonzero)>=5 and all(ms[j][0]+ms[j][3]==2 for j in nonzero):
   supp=self.mask_poly(nonzero,step);a=self.poly([m[0] for m in ms],step);bb=self.poly([m[1] for m in ms],step)
   w=Counter(ms[j][2] for j in nonzero).most_common(1)[0][0]
   correction=self.poly([m[2]-w if any(m) else 0 for m in ms],step)
   cc=self.add(self.mul(w,supp),correction);dd=self.sub(self.mul(2,supp),a)
   want=tuple(1 if j%step==0 and j//step in nonzero else 0 for j in range(step*max(nonzero)+1));ck(self.val(supp)==want,'support factorization')
   out=[a,bb,cc,dd]
   for j in range(4):
    co=trim([ms[k//step][j] if k%step==0 else 0 for k in range(step*(len(ms)-1)+1)]);ck(self.val(out[j])==co,'trace matrix entry identity')
   self.trace_records.append({'step':step,'support_indices':nonzero,'matrices':[ms[j] for j in nonzero],'common_lower_left':w,'outputs':out})
   return out
  return [self.poly([a[j] for a in ms],step) for j in range(4)]
 def rowmat(self,v,m):return [self.add(self.mul(v[0],m[j]),self.mul(v[1],m[j+2])) for j in [0,1]]
 def rowsum(self,vs):return [self.sum(v[i] for v in vs) for i in [0,1]]
 def scale(self,v,p):return [self.mul(t,p) for t in v]

def component(parent,raw):
 Q=parent['ports']['Q'];insert=sum(parent['stage_counts'][s] for s in ['packing','native']);b=DAG(Q,parent['source'][:insert]);letters=raw['packet']['letters'];tiles=raw['packet']['tiles'];C=[-31653619,195915076,-3702035,22913161];CI=inv(C)
 groups=parent['groups'];ck(groups[-2]['kind']=='LOAD' and groups[-2]['matrix']==inv(word('01010111'*2,letters)),'fixed LOAD word');Kg=[g for g in groups if g['kind']=='K'];Gg=[g for g in groups if g['kind']=='G'];ck(len(Kg)==72 and len(Gg)==96,'group counts')
 words={side:[tiles[g['edges'][0]-2][port] for g in gs] for side,port,gs in [('X','h',Kg),('Y','g',Gg)]}
 for gs,side in [(Kg,'X'),(Gg,'Y')]:
  for g,w in zip(gs,words[side]):
   mat=word(w,letters);mat=mm(mm(CI,mat),C) if side=='X' else mat;ck(mat==g['matrix'],'word matrix');ck(all(tiles[e-2]['h' if side=='X' else 'g']==w for e in g['edges']),'same word group')
 ck(words['X'][:4]==list('01[]') and words['Y'][:4]==list('01[]'),'copy prefix')
 ck(words['X'][-2:]==['J1','#'] and words['Y'][-5:]==['0J1','J10','1J1','J11','#'],'tails')
 pref=b.matrix_poly([letters[x] for x in '] [ 1 0'.split()],2)
 # Shared quadratic right suffixes and left prefixes, listed constant first.
 CR=b.matrix_poly([letters[']'],letters['1'],letters['0']],2)
 CL=b.matrix_poly([letters['['],letters['1'],letters['0']],2)
 DR=b.matrix_poly([word('0]',letters),letters['1'],letters['0']],2)
 D01=b.matrix_poly([[0]*4,letters['1'],letters['0']],2)
 outputs={};records={}
 for side in ['X','Y']:
  n=72 if side=='X' else 97;jcount=22 if side=='X' else 29;cats=['R','L0','L1'] if side=='X' else ['R','L'];seqs={cat:[[0]*4 for _ in range(jcount)] for cat in cats};audit=[]
  for j in range(jcount):
   ws=words[side][4+3*j:7+3*j]
   if ws[2].endswith(']'):
    aa=ws[0][:-1];ck(ws==([aa+'0',aa+'1',aa+'0]'] if side=='X' else [aa+'0',aa+'1',aa+']']),'right triple');cat='R'
   else:
    ck(ws[2].startswith('['),'left triple')
    if side=='X':
     pp=ws[0][0];bb=ws[0][-1];ck(ws==[pp+'0'+bb,pp+'1'+bb,'['+pp+'0'+bb],'X left');aa=pp;cat='L'+bb
    else:
     aa=ws[0][1:];ck(ws==['0'+aa,'1'+aa,'['+aa],'Y left');cat='L'
   seqs[cat][jcount-1-j]=word(aa,letters);audit.append({'words':ws,'category':cat,'factor_word':aa})
  v=b.rowmat([Q,1],CI) if side=='X' else [Q,1]
  if side=='X':
   mats={cat:b.matrix_poly(seq,6) for cat,seq in seqs.items()}
   right=b.rowmat(b.rowmat(v,mats['R']),DR)
   left=[b.rowmat(b.rowsum([b.rowmat(b.rowmat(v,mats[cat]),D01),b.rowmat(b.rowmat(b.rowmat(v,letters['[']),mats[cat]),letters['0'])]),letters[cat[-1]]) for cat in ['L0','L1']]
   triple=b.rowsum([right]+left)
  else:
   states={}
   for j,rec in enumerate(audit):
    q,a=rec['factor_word'];states.setdefault(q,{})[a]=(j,rec['category'])
   paired={cat:[[0]*4 for _ in range(jcount)] for cat in ['RR','LL','RL','LR']};single=[]
   for q,items in states.items():
    if len(items)==2:
     j0,cat0=items['0'];j1,cat1=items['1'];ck(j1==j0+1,'adjacent read pair');paired[cat0+cat1][jcount-1-j1]=letters[q]
    else:
     ck(q=='J' and set(items)=={'0'} and items['0'][1]=='L','single J0');single.append((q,jcount-1-items['0'][0]))
   mats={cat:b.matrix_poly(seq,6) for cat,seq in paired.items()};pair=b.matrix_poly([letters['1'],letters['0']],6);vL=b.rowmat(v,CL)
   Rrow=b.rowsum([b.rowmat(b.rowmat(v,mats['RR']),pair),b.scale(b.rowmat(b.rowmat(v,mats['RL']),letters['0']),b.pow(6)),b.rowmat(b.rowmat(v,mats['LR']),letters['1'])])
   Lrow=b.rowsum([b.rowmat(b.rowmat(vL,mats['LL']),pair),b.rowmat(b.rowmat(vL,mats['RL']),letters['1']),b.scale(b.rowmat(b.rowmat(vL,mats['LR']),letters['0']),b.pow(6))]+[b.scale(b.rowmat(b.rowmat(vL,letters[q]),letters['0']),b.pow(6*e)) for q,e in single])
   triple=b.rowsum([b.rowmat(Rrow,CR),Lrow])
  prefix=b.scale(b.rowmat(v,pref),b.pow(2*(n-4)))
  if side=='X':tailm=b.matrix_poly([letters['#'],word('J1',letters)],2)
  else:tailm=b.matrix_poly([groups[-2]['matrix']]+[word(w,letters) for w in reversed(words['Y'][-5:])],2)
  total=b.rowsum([prefix,b.scale(triple,b.pow(2*(n-4-3*jcount))),b.rowmat(v,tailm)])
  if side=='X':total=b.rowmat(total,C)
  rr=b.rep2(n);total=[b.sub(total[0],b.mul(Q,rr)),b.sub(total[1],rr)]
  for j,old in enumerate(parent['extraction'][0 if side=='X' else 1]['products']):ck(b.val(total[j])==tuple(reversed(old['coefficients'])),'full coefficient equality '+side+str(j))
  outputs[side]=total;records[side]={'triples':audit,'categories':{cat:sum(any(a) for a in seq) for cat,seq in seqs.items()},'outputs':total}
  if side=='Y':records[side]['read_pair_groups']={cat:[{'exponent':j,'matrix':a} for j,a in enumerate(seq) if any(a)] for cat,seq in paired.items()};records[side]['single']=[list(x) for x in single]
 return b,outputs,records,insert

def splice(parent,raw):
 b,out,records,insert=component(parent,raw)
 replacement={prod['polynomial']:out[side][j] for rec in parent['extraction'] for side in [rec['side']] for j,prod in enumerate(rec['products'])}
 before=parent['source'][:insert]
 after=[[n,op,replacement.get(l,l),replacement.get(r,r)] for n,op,l,r in parent['source'][insert:]]
 rows=before+b.rows+after;deps={n:(l,r) for n,op,l,r in rows};live=set();todo=[parent['output']]
 while todo:
  t=todo.pop()
  if type(t)is str and t not in live:live.add(t);todo.extend(deps.get(t,()))
 rows=[row for row in rows if row[0] in live]
 ck(set(parent['free'])<=live,'free interface lost')
 known=set(parent['free'])
 for n,op,l,r in rows:
  ck(n not in known,'duplicate');ck(all(type(v)is int or v in known for v in [l,r]),'topology');known.add(n)
 ck(known==live,'whole liveness')
 removed=[n for n,op,l,r in parent['source'] if n not in live]
 added=[r for r in b.rows if r[0] in live]
 ct=Counter(r[1] for r in rows)
 return {'source':rows,'free':parent['free'],'fixed_numerals':parent['fixed_numerals'],'witnesses':parent['witnesses'],'output':parent['output'],'replacement':replacement,'removed_parent_rows':removed,'coefficient_component':added,'emitted_component_rows':len(b.rows),'discarded_component_rows':len(b.rows)-len(added),'structural_records':records,'ledger':{'total':len(rows),'M':ct['*'],'A':ct['+']+ct['-'],'positive_witnesses':len(parent['witnesses']),'all_live':True,'degree':35587}},b


def sha(b):return hashlib.sha256(b).hexdigest()
def parse(path):
 def obj(items):
  d={}
  for k,v in items:ck(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(path.read_text(),object_pairs_hook=obj)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def coefficient_audit(parent,p):
 # Independent sparse expansion of the emitted rows, treating only Q as an indeterminate.
 Q=parent['ports']['Q'];values={Q:{1:1}};saved={};targets=set(p['replacement'].values());original={}
 def val(t):return {} if t==0 else {0:t} if type(t)is int else values[t]
 def step(op,a,b):
  d={}
  if op=='*':
   for i,x in a.items():
    for j,y in b.items():d[i+j]=d.get(i+j,0)+x*y
  else:
   d=dict(a)
   for j,y in b.items():d[j]=d.get(j,0)+(y if op=='+' else -y)
  return {i:x for i,x in d.items() if x}
 for n,op,l,r in p['source']:
  if n==Q:continue
  if (type(l)is int or l in values) and (type(r)is int or r in values):
   values[n]=step(op,val(l),val(r))
   if n in targets:saved[n]=values[n]
 cert=[]
 for rec in parent['extraction']:
  for j,prod in enumerate(rec['products']):
   old=prod['polynomial'];new=p['replacement'][old];co=list(reversed(prod['coefficients']));want={i:x for i,x in enumerate(co) if x}
   ck(saved[new]==want,'independent full coefficient expansion')
   cert.append({'side':rec['side'],'column':j,'old_output':old,'new_output':new,'degree_in_Q':len(co)-1,'ascending_coefficients':co,'sha256':sha(json.dumps(co,separators=(',',':')).encode())})
 return cert

def source_identity(parent,p):
 # Treat the four proved coefficient identities as formal cut atoms, then intern
 # every surrounding operation. This proves the complete polynomial identity.
 cache={};nextid=[0]
 def ident(k):
  if k not in cache:cache[k]=nextid[0];nextid[0]+=1
  return cache[k]
 common={v:ident(('free',v)) for v in parent['free']}
 ports={old:ident(('coefficient_cut',j)) for j,old in enumerate(p['replacement'])}
 def run(packet,cuts):
  env=dict(common)
  for n,op,l,r in packet['source']:
   li=ident(('integer',l)) if type(l)is int else env[l];ri=ident(('integer',r)) if type(r)is int else env[r]
   env[n]=cuts[n] if n in cuts else ident((op,li,ri))
  return env
 a=run(parent,ports);b=run(p,{p['replacement'][old]:v for old,v in ports.items()});retained=0
 for n,op,l,r in parent['source']:
  if n in b:ck(a[n]==b[n],'retained surrounding row '+n);retained+=1
 ck(a[parent['output']]==b[p['output']],'whole formal identity')
 ck(retained==len(parent['source'])-633,'exact old cone removal')
 oldnames={r[0] for r in parent['source']};newnames={r[0] for r in p['source']}
 # Four original producers have no other consumers outside their private cones.
 removed=set(p['removed_parent_rows']);allowed=set(p['replacement'])
 for n,op,l,r in parent['source']:
  if n not in removed:ck(all(v not in removed or v in allowed for v in [l,r]),'private removed cone')
 return {'four_coefficient_cuts':4,'retained_parent_rows':retained,'removed_private_rows':len(removed),'inserted_live_rows':len(newnames-oldnames),'identical_full_polynomial':True,'domain':'all commutative rings under the same numeral interpretation'}

def eval_rows(p,bind,mod):
 env=dict(bind)
 for n,op,l,r in p['source']:
  a=env[l] if type(l)is str else l;b=env[r] if type(r)is str else r
  env[n]=(a*b if op=='*' else a+b if op=='+' else a-b)%mod
 return env

def modular_checks(parent,p):
 rng=random.Random(1803);ans=[]
 for modulus in [1000000007,1000000009]:
  for case in range(16):
   v={x:rng.randrange(-100,101) for x in parent['free']}
   if case%2==0:v.update(parent['fixture_fixed_bindings'])
   a=eval_rows(parent,v,modulus);b=eval_rows(p,v,modulus)
   for n,op,l,r in parent['source']:
    if n in b:ck(a[n]==b[n],'full modular retained row')
   for old,new in p['replacement'].items():ck(a[old]==b[new],'modular polynomial cut')
   ck(a[parent['output']]==b[p['output']],'modular whole output');ans.append({'modulus':modulus,'case':case,'fixture_fixed_ports':case%2==0,'output':b[p['output']]})
 return ans

def run(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'pin '+n)
 old=parse(root/'matrix193_composed_output_scout.json');ck(old['source_sha256']==PINS['matrix193_composed_output_scout.py'],'parent source/receipt pin');parent=old['packets'][1];raw=parse(root/'matrix193_gamma1_recode.json');p,b=splice(parent,raw)
 p['coefficient_certificates']=coefficient_audit(parent,p);p['complete_identity']=source_identity(parent,p);p['trace_two_records']=b.trace_records;p['affine_interning_events']=len(b.affine_hits)
 p['fixture_fixed_bindings']=parent['fixture_fixed_bindings'];p['ports']=copy.deepcopy(parent['ports']);p['native_cut_bindings']=copy.deepcopy(parent['native_cut_bindings']);p['comparisons']=copy.deepcopy(parent['comparisons']);p['extraction']=copy.deepcopy(parent['extraction'])
 for rec in p['extraction']:
  for prod in rec['products']:prod['polynomial']=p['replacement'][prod['polynomial']]
 ct=Counter(row[1] for row in p['coefficient_component']);p['component_ledger']={'total':len(p['coefficient_component']),'M':ct['*'],'A':ct['+']+ct['-']};p['ledger'].update(saving=parent['ledger']['total']-p['ledger']['total'],residuals=20,literal_count=len({v for row in p['source'] for v in row[2:] if type(v)is int}))
 ck((p['ledger']['total'],p['ledger']['M'],p['ledger']['A'],len(p['witnesses']))==(1624,791,833,146),'full ledger');ck(len(p['coefficient_component'])==578 and len(p['removed_parent_rows'])==633,'component edit')
 ck(len(p['trace_two_records'])==4,'four trace-two components');ck({k:len(v) for k,v in p['structural_records']['Y']['read_pair_groups'].items()}=={'RR':5,'LL':5,'RL':2,'LR':2},'paired state counts')
 return {'schema':'matrix193-entry-shared-coefficients-v1','pins':PINS,'source_sha256':sha(Path(__file__).read_bytes()),'status':'complete all-value successor of the frozen composed1679 matrix polynomial','scope':{'predecessor_code_executed':False,'identity_on_every_supplied_coordinate':True,'same_146_positive_witnesses':True,'established_universal84_unchanged':True,'new_giant_fixture_or_native_Pell_claim':False},'packet':p,'modular_checks':modular_checks(parent,p),'unchanged_diagnostic':{'source_sha256':sha(json.dumps(old['packets'][0]['source'],separators=(',',':')).encode()),'ledger':old['packets'][0]['ledger'],'no_new_diagnostic_source_claim':True},'degree_proof':{'exact':35587,'reason':'whole polynomial equals the pinned composed parent on identical supplied coordinates, including bounded high hats; its SWITCH degree-tie proof transfers without alteration'},'inherited_outer_evidence_replayed':False}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--write',type=Path);g.add_argument('--expect',type=Path);args=ap.parse_args();r=run(args.root)
 if args.write:args.write.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(exact(r,parse(args.expect)),'exact typed receipt mismatch')
 print('PASS: complete1624=791M+833A/146w;four exact coefficient cuts;1046 retained rows/full output identical;32 modular checks')
if __name__=='__main__':main()
