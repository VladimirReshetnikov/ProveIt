#!/usr/bin/env python3
"""Fresh structured word-polynomial compiler; predecessor JSON is inert data."""
import json,hashlib,argparse,random,copy
from pathlib import Path
from collections import Counter
PINS={'matrix193_balanced_output_scout.py':'e567a5be0cb656dfc984aa86fb306584dd837b7c24568659af222c781266d76a','matrix193_balanced_output_scout.json':'63a4b6b269ba177603cbebec51848bc6fbcd3c04115bb3dbb367dd63a2f7c9bf','matrix193_balanced_output_scout.md':'cfc892b2c7a577d2348c3583d968e04ab271f065003cc0bfa6316a9f05f3abde','matrix193_gamma1_recode.json':'9cdd0274625c847aa77f5907ba6554ee16f37895f5c026b3d776595330676668','matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742'}
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
  n='cp'+str(len(self.rows));self.rows.append([n,op,a,b]);self.values[n]=v;self.known[v]=n;return n
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
 def matrix_poly(self,ms,step=1):return [self.poly([a[j] for a in ms],step) for j in range(4)]
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
  mats={cat:b.matrix_poly(seq,6) for cat,seq in seqs.items()};v=b.rowmat([Q,1],CI) if side=='X' else [Q,1]
  if side=='X':
   right=b.rowmat(b.rowmat(v,mats['R']),DR)
   left=[b.rowmat(b.rowsum([b.rowmat(b.rowmat(v,mats[cat]),D01),b.rowmat(b.rowmat(b.rowmat(v,letters['[']),mats[cat]),letters['0'])]),letters[cat[-1]]) for cat in ['L0','L1']]
   triple=b.rowsum([right]+left)
  else:triple=b.rowsum([b.rowmat(b.rowmat(v,mats['R']),CR),b.rowmat(b.rowmat(v,CL),mats['L'])])
  prefix=b.scale(b.rowmat(v,pref),b.pow(2*(n-4)))
  if side=='X':tailm=b.matrix_poly([letters['#'],word('J1',letters)],2)
  else:tailm=b.matrix_poly([groups[-2]['matrix']]+[word(w,letters) for w in reversed(words['Y'][-5:])],2)
  total=b.rowsum([prefix,b.scale(triple,b.pow(2*(n-4-3*jcount))),b.rowmat(v,tailm)])
  if side=='X':total=b.rowmat(total,C)
  rr=b.rep2(n);total=[b.sub(total[0],b.mul(Q,rr)),b.sub(total[1],rr)]
  for j,old in enumerate(parent['extraction'][0 if side=='X' else 1]['products']):ck(b.val(total[j])==tuple(reversed(old['coefficients'])),'full coefficient equality '+side+str(j))
  outputs[side]=total;records[side]={'triples':audit,'categories':{cat:sum(any(a) for a in seq) for cat,seq in seqs.items()},'outputs':total}
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
 ck(retained==len(parent['source'])-1344,'exact old cone removal')
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
 old=parse(root/'matrix193_balanced_output_scout.json');parent=old['packets'][1];raw=parse(root/'matrix193_gamma1_recode.json');p,b=splice(parent,raw)
 p['coefficient_certificates']=coefficient_audit(parent,p);p['complete_identity']=source_identity(parent,p)
 p['fixture_fixed_bindings']=parent['fixture_fixed_bindings'];p['ports']=copy.deepcopy(parent['ports']);p['native_cut_bindings']=copy.deepcopy(parent['native_cut_bindings']);p['comparisons']=copy.deepcopy(parent['comparisons']);p['extraction']=copy.deepcopy(parent['extraction'])
 for rec in p['extraction']:
  for product in rec['products']:product['polynomial']=p['replacement'][product['polynomial']]
 ct=Counter(r[1] for r in p['coefficient_component']);p['component_ledger']={'total':len(p['coefficient_component']),'M':ct['*'],'A':ct['+']+ct['-']}
 p['ledger']['saving']=parent['ledger']['total']-p['ledger']['total'];p['ledger']['residuals']=len(parent['comparisons']);p['ledger']['fixed_numerals_distinct']=len({v for row in p['source'] for v in row[2:] if type(v)is int})
 ck(p['ledger']['total']==1756 and p['ledger']['M']==795 and p['ledger']['A']==961 and len(p['witnesses'])==150,'final ledger')
 ck(p['component_ledger']['total']==638 and p['discarded_component_rows']==0,'component ledger')
 # The tiny controller lacks the U15 word grammar. Save its complete unchanged
 # diagnostic array, explicitly outside the structural saving claim.
 diagnostic=copy.deepcopy(old['packets'][0]);de=eval_rows(diagnostic,{x:3 for x in diagnostic['free']},1000000007)
 return {'schema':'matrix193-structured-coefficient-scout-v1','pins':PINS,'source_sha256':sha(Path(__file__).read_bytes()),'status':'complete all-value arithmetic rewrite of frozen balanced2462; inherited ordinary-input representation','scope':{'predecessor_code_executed':False,'same_150_positive_witnesses':True,'new_universal_bound_below84':False,'fixed_numerals_recipe':'exact matrix words, signed products/sums and emitted powers; no variable division','new_accepting_or_native_Pell_fixture_claim':False},'packet':p,'modular_checks':modular_checks(parent,p),'diagnostic_unchanged':diagnostic,'diagnostic_reference_check':{'modulus':1000000007,'all_free_ports_value':3,'output':de[diagnostic['output']],'saving_claim':False},'inherited_degree':{'exact':35587,'reason':'proved complete all-value identity with the pinned balanced polynomial; no new dense expansion claimed','diagnostic_exact_unchanged':1363},'ancestor_evidence_scope':{'actual_outer_fixture':old['actual_atomic_outer_fixture'],'new_fixture_replay':False}}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--write',type=Path);g.add_argument('--expect',type=Path);args=ap.parse_args();receipt=run(args.root)
 if args.write:args.write.write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
 else:ck(exact(receipt,parse(args.expect)),'exact typed receipt mismatch')
 print('PASS: complete1756=795M+961A;150w;four exact coefficient identities;full all-value source identity;32 modular checks')
if __name__=='__main__':main()
