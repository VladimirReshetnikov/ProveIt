#!/usr/bin/env python3
"""Independent inert-data audit; imports no author or predecessor program."""
import argparse
import hashlib
import json
import random
from collections import Counter
from pathlib import Path

PARENT_SHA='63a4b6b269ba177603cbebec51848bc6fbcd3c04115bb3dbb367dd63a2f7c9bf'

def require(ok,msg):
 if not ok: raise ValueError(msg)

def sha(b): return hashlib.sha256(b).hexdigest()

def read(path):
 def pairs(items):
  d={}
  for k,v in items:
   require(k not in d,'duplicate key');d[k]=v
  return d
 return json.loads(path.read_text(),object_pairs_hook=pairs)

def enc(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()

def number(n): return {():n} if n else {}
def variable(v): return {((v,1),):1}
def combine(p,q,sign=1):
 out=p.copy()
 for key,value in q.items():
  out[key]=out.get(key,0)+sign*value
  if not out[key]: del out[key]
 return out
def multiply(p,q):
 out={}
 for first,a in p.items():
  for second,b in q.items():
   powers=Counter(dict(first));powers.update(dict(second));key=tuple(sorted(powers.items()))
   out[key]=out.get(key,0)+a*b
 return {k:v for k,v in out.items() if v}

class Algebra:
 def __init__(self,packet,cut_q):
  self.rows={r[0]:r for r in packet['source']};self.free=set(packet['free']);self.memo={}
  if cut_q:self.memo[packet['ports']['Q']]=variable('@Q')
 def value(self,x):
  if type(x)is int:return number(x)
  if x not in self.memo:
   if x in self.free:self.memo[x]=variable(x)
   else:
    _,op,l,r=self.rows[x];a,b=self.value(l),self.value(r)
    self.memo[x]=multiply(a,b) if op=='*' else combine(a,b,1 if op=='+' else -1)
  return self.memo[x]
 def atomize(self,x,name):self.memo[x]=variable(name)

def audit_graph(p):
 known=set(p['free']);edges={};counts=Counter()
 require(len(known)==len(p['free']),'unique free ports')
 for name,op,a,b in p['source']:
  require(name not in known,'unique produced wire');require(op in ['+','-','*'],'operation')
  require(all(type(v)is int or v in known for v in [a,b]),'topology')
  known.add(name);edges[name]=(a,b);counts[op]+=1
 live=set();pending=[p['output']]
 while pending:
  v=pending.pop()
  if type(v)is str and v not in live:
   live.add(v);pending.extend(edges.get(v,()))
 require(live==known,'complete output liveness')
 ledger={'total':len(p['source']),'M':counts['*'],'A':counts['+']+counts['-'],'witnesses':len(p['witnesses'])}
 require(ledger['total']==p['ledger']['total'] and ledger['M']==p['ledger']['M'] and ledger['A']==p['ledger']['A'],'emitted operation count')
 require(ledger['witnesses']==p['ledger']['positive_witnesses'],'witness count')
 return ledger

def registry_check(p):
 groups=p['groups'];nx=sum(g['source_coordinate']==0 for g in groups)
 x=[len(g['edges']) for g in groups[:nx]];y=[len(g['edges']) for g in groups[nx:-1]]
 require(groups[-1]['kind']=='SWITCH' and groups[-1]['edges']==[1],'switch group')
 if len(x)==72:
  predicted=[1]*72
  for outer in [0,18]:
   for inner,weight in [(0,2),(24,1)]:
    for j in range(3):predicted[7+j+outer+inner]+=weight
  for j in range(3):predicted[7+j+48]+=1
  predicted[70]+=3
  require(x==predicted,'complete compact X cardinality polynomial')
  require(len(y)==97 and y==[1]*97,'Y correction R98-t97')
 else: require(x==[1] and y==[1],'diagnostic cardinalities')
 require(groups[-2]['kind']=='LOAD' and groups[-2]['edges']==[0],'raw LOAD group')
 return {'X_coefficients':x,'Y_coefficients':y,'X_edge_coverage':sum(x),'Y_edge_coverage':sum(y)}

def skeleton(p,native_labels=False):
 start=p['stage_counts']['packing'];reverse={v:k for k,v in p['native_cut_bindings'].items()}
 return [[r[0],r[1],reverse.get(r[2],r[2]),reverse.get(r[3],r[3])] for r in p['source'][start:start+63]]

def check_finalizer(p):
 tail=p['source'][-62:];names={};out=[]
 for j,(l,r) in enumerate(p['comparisons']):
  a,b=tail[2*j],tail[2*j+1]
  require(a[1:]==['-',l,r] and b[1:]==['*',a[0],a[0]],'residual square')
  names[a[0]]='residual'+str(j);names[b[0]]='square'+str(j)
 for row in tail[40:]:
  mapped=[row[1]]+[names.get(x,x) for x in row[2:]]
  names[row[0]]='join'+str(len(out));out.append(mapped)
 return out

def exact_identity(old,new):
 require(old['free']==new['free'] and old['witnesses']==new['witnesses'],'same supplied interface')
 require(old['groups']==new['groups'],'same complete coefficient groups')
 a0,b0=Algebra(old,False),Algebra(new,False)
 old_q,new_q=a0.value(old['ports']['Q']),b0.value(new['ports']['Q'])
 require(old_q==new_q,'entire Q definition without boundary cuts')
 a,b=Algebra(old,True),Algebra(new,True)
 word_counts=[]
 for j,(or_,nr) in enumerate(zip(old['extraction'],new['extraction'])):
  require(or_['length']==nr['length'],'same block lengths')
  for k,(op,np) in enumerate(zip(or_['products'],nr['products'])):
   require(op['coefficients']==np['coefficients'],'unchanged signed coefficients')
   x,y=a.value(op['polynomial']),b.value(np['polynomial']);require(x==y,'expanded entire coefficient polynomial')
   word_counts.append(len(x));a.atomize(op['polynomial'],'@word'+str(2*j+k));b.atomize(np['polynomial'],'@word'+str(2*j+k))
 cuts={}
 require(old['native_cut_bindings'].keys()==new['native_cut_bindings'].keys(),'same native interface')
 for name,wire in old['native_cut_bindings'].items():
  x,y=a.value(wire),b.value(new['native_cut_bindings'][name]);require(x==y,'expanded full native cut '+name);cuts[name]=len(x)
 require(skeleton(old)==skeleton(new),'all63 literal native rows')
 sizes=[]
 for i,((x,y),(z,w)) in enumerate(zip(old['comparisons'],new['comparisons'])):
  p=combine(a.value(x),a.value(y),-1);q=combine(b.value(z),b.value(w),-1)
  require(p==q,'expanded complete residual '+str(i));sizes.append(len(p))
 require(len(sizes)==20,'all twenty residuals')
 require(check_finalizer(old)==check_finalizer(new),'complete62-row finalizer')
 return {'identity':'new polynomial equals the full balanced parent at identical supplied coordinates',
         'uncut_Q_definition_terms':len(old_q),'sole_initial_shared_atom':'proved complete Q',
         'fully_checked_coefficient_word_terms':word_counts,'native_cut_terms':cuts,
         'full_residual_terms':sizes,'native_literal_rows':63,'finalizer_literal_rows':62}

def values(p,v,mod):
 e=dict(v)
 for name,op,l,r in p['source']:
  a=e[l] if type(l)is str else l;b=e[r] if type(r)is str else r
  e[name]=(a*b if op=='*' else a+b if op=='+' else a-b)%mod
 return e[p['output']]

def run(root,author):
 parent_path=root/'matrix193_balanced_output_scout.json';require(sha(parent_path.read_bytes())==PARENT_SHA,'parent pin')
 old=read(parent_path);new=read(author/'matrix193_hat_packing_scout.json')
 require(len(new['pins'])==9,'nine author dependencies')
 for name,pin in new['pins'].items():require(sha((root/name).read_bytes())==pin,'dependency '+name)
 require(sha((author/'matrix193_hat_packing_scout.py').read_bytes())==new['source_sha256'],'author self source pin')
 answer=[]
 for previous,current in zip(old['packets'],new['packets']):
  row={'name':current['name'],'ledger':audit_graph(current),'registry':registry_check(current),'exact_algebra':exact_identity(previous,current)}
  rng=random.Random(9173+current['n']);numbers=[]
  for mod in [1000000007,1000000009]:
   for j in range(12):
    v={s:rng.randrange(-99,100) for s in current['free']}
    if j<6:v.update(current['fixture_fixed_bindings'])
    x,y=values(current,v,mod),values(previous,v,mod);require(x==y,'independent complete modular comparison');numbers.append([mod,j,x])
  row['complete_modular_comparisons']=numbers;answer.append(row)
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'parent_json_sha256':PARENT_SHA,
         'author_hashes':{ext:sha((author/('matrix193_hat_packing_scout.'+ext)).read_bytes()) for ext in ['py','json','md']},
         'dependency_pins':new['pins'],'arrays':answer,'scope':'Full literal graph, exact algebra at one proved Q cut and four fully verified coefficient words; no author execution or native tuple.'}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path,default=Path('/tmp'))
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);args=ap.parse_args()
 result=run(args.root,args.author_root)
 if args.output:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 else:require(enc(result)==enc(read(args.expect)),'exact receipt')
 print(json.dumps({'status':'PASS','ledgers':[r['ledger'] for r in result['arrays']]}))
