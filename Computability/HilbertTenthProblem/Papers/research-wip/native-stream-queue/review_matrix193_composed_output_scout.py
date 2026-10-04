#!/usr/bin/env python3
"""Independent inert-data audit; imports no author or predecessor program."""
import argparse
import hashlib
import json
import random
from collections import Counter
from pathlib import Path

PARENT_SHA='9fee15c95d916813f425db0f306c9f0e50990540fe9284fc00c46cc380cb5039'
AUTHOR_PINS={
 'py':'e8b2982bdf00a9be6e6e80a1b86c38f3536a5345c60adf3103e8f7356ed01317',
 'json':'a231b3ef66f0ab0f729bf50e40f87fad5a5d784e089249dbb4e93e11696a9e37',
 'md':'83711eab17b18f38c2bd47ddd3d803fde5adf339f7b5bbc0be2839a3bfeff748'}

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
 known=set(p['free']);edges={};counts=Counter();degree={s:int(s not in p['fixed_numerals']) for s in p['free']}
 require(len(known)==len(p['free']),'unique free ports')
 for name,op,a,b in p['source']:
  require(name not in known,'unique produced wire');require(op in ['+','-','*'],'operation')
  require(all(type(v)is int or v in known for v in [a,b]),'topology')
  known.add(name);edges[name]=(a,b);counts[op]+=1
  degree[name]=degree.get(a,0)+degree.get(b,0) if op=='*' else max(degree.get(a,0),degree.get(b,0))
 live=set();pending=[p['output']]
 while pending:
  v=pending.pop()
  if type(v)is str and v not in live:
   live.add(v);pending.extend(edges.get(v,()))
 require(live==known,'complete output liveness')
 ledger={'total':len(p['source']),'M':counts['*'],'A':counts['+']+counts['-'],'witnesses':len(p['witnesses'])}
 require(ledger['total']==p['ledger']['total'] and ledger['M']==p['ledger']['M'] and ledger['A']==p['ledger']['A'],'emitted operation count')
 require(ledger['witnesses']==p['ledger']['positive_witnesses'],'witness count')
 require(sum(p['stage_counts'].values())==ledger['total'],'complete stage ledger')
 require(p['stage_counts']['native']==63 and p['stage_counts']['finalizer']==62,'retained stages')
 literals={v for row in p['source'] for v in row[2:] if type(v)is int}
 require(len(literals)==p['ledger']['literal_count'],'literal count')
 require(degree[p['output']]==p['ledger']['syntactic_degree_upper'],'syntactic upper degree')
 ledger.update({'stages':p['stage_counts'],'literal_count':len(literals),'syntactic_upper':degree[p['output']]})
 return ledger

def degree_certificate(p,old):
 require(p['fixed_numerals']==old['fixed_numerals'],'same degree-zero fixed ports')
 offset=0;checks=[]
 for rec in p['extraction']:
  require(rec['length']%2==0,'paired coefficient block')
  last=p['groups'][offset+rec['length']//2-1]
  require(1 not in last['edges'],'independent SWITCH variable absent from final selector')
  checks.append({'length':rec['length'],'last_edges':last['edges'],'residual_degree':4*rec['length']-2})
  offset+=rec['length']//2
 require(p['padding']>0 and p['padding']%2==0,'nonzero paid integer half padding')
 require(p['groups'][-1]['kind']=='SWITCH' and p['groups'][-1]['edges']==[1],'literal independent switch')
 residual=max(x['residual_degree'] for x in checks)
 native=34039 if p['n']==99 else 1351
 degree=native+2*residual
 require(degree==p['ledger']['proved_exact_degree']==old['ledger']['proved_exact_degree'],'degree transferred by full polynomial identity')
 return {'blocks':checks,'native_degree_inherited_from_pinned_parent':native,'exact_degree':degree,
         'nonzero_bracket_reason':'SWITCH coefficient C*K/2 in (C*K/2)*J_top-a0*S_last_top',
         'proof_scope':'Uniform valid fixed recipe; native degree inherited, exact full identity independently checked.'}

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
 return {'identity':'new polynomial equals the full bounded-high parent at identical supplied coordinates',
         'uncut_Q_definition_terms':len(old_q),'sole_initial_shared_atom':'proved complete Q',
         'fully_checked_coefficient_word_terms':word_counts,'native_cut_terms':cuts,
         'full_residual_terms':sizes,'native_literal_rows':63,'finalizer_literal_rows':62}

def values(p,v,mod):
 e=dict(v)
 for name,op,l,r in p['source']:
  a=e[l] if type(l)is str else l;b=e[r] if type(r)is str else r
  e[name]=(a*b if op=='*' else a+b if op=='+' else a-b)%mod
 return e[p['output']]

def q_coefficients(poly):
 out={}
 for monomial,c in poly.items():
  require(all(name=='@Q' for name,e in monomial),'pure Q expression')
  exponent=sum(e for name,e in monomial);out[exponent]=c
 return [out.get(j,0) for j in range(max(out,default=-1)+1)]

def composition_check(hat,balanced,structured,new):
 insert=hat['stage_counts']['packing']+63
 indices={row[0]:j for j,row in enumerate(hat['source'])}
 hs,bs=Algebra(hat,True),Algebra(balanced,True)
 audit=new['composition'];component=audit['live_component_rows'];replacement=audit['replacement']
 require(component==[r for r in new['source'] if r[0].startswith('mix')],'all literal component rows')
 binding_record=[];merge_record=[]
 if structured is not None:
  original=structured['coefficient_component'];defined={r[0] for r in original}
  external={v for r in original for v in r[2:] if type(v)is str and v not in defined}
  declared=audit['coefficient_splice']['external_equal_Q_bindings']
  require(len(external)==len(declared)==13 and external=={r['structured_parent_register'] for r in declared},'all thirteen external bindings')
  mapping={};env={}
  for r in declared:
   old,target=r['structured_parent_register'],r['hat_parent_register']
   require(target in indices and indices[target]<insert,'binding available in paid prefix')
   poly=bs.value(old);require(poly==hs.value(target),'full external Q equality')
   coeff=q_coefficients(poly);require(coeff==r['ascending_coefficients_in_Q'],'external coefficient certificate')
   mapping[old]=target;env[old]=poly;binding_record.append({'old':old,'prefix':target,'degree':len(coeff)-1,'coefficient_sha256':sha(enc(coeff))})
  merged=audit['coefficient_splice']['reused_component_rows']
  require(len(merged)==5,'five component merges')
  reused={r['component_register']:r['reused_register'] for r in merged}
  require(len(reused)==5,'distinct merged producers')
  emitted=0
  for name,op,l,r in original:
   a=number(l) if type(l)is int else env[l];b=number(r) if type(r)is int else env[r]
   poly=multiply(a,b) if op=='*' else combine(a,b,1 if op=='+' else -1);env[name]=poly
   if name in reused:
    target=reused[name];require(target in indices and indices[target]<insert,'merged value already paid in prefix')
    require(poly==hs.value(target),'exact complete merged polynomial');mapping[name]=target
    merge_record.append({'old':name,'prefix':target,'ascending_coefficients':q_coefficients(poly)})
   else:
    row=component[emitted];require(row==['mix'+str(emitted),op,mapping.get(l,l),mapping.get(r,r)],'literal transplanted component row')
    mapping[name]=row[0];emitted+=1
  require(emitted==633 and len(original)==638,'complete component accounting')
  wanted=[[0]*e+[1] for e in [17,34,97,194]]+[[int(j%2==0) for j in range(193)]]
  require(sorted(enc(r['ascending_coefficients']) for r in merge_record)==sorted(enc(x) for x in wanted),'specified four powers and R97(Q squared)')
  expected_replacement={}
  for hr,br,nr in zip(hat['extraction'],balanced['extraction'],new['extraction']):
   for hp,bp,np in zip(hr['products'],br['products'],nr['products']):
    target=mapping[structured['replacement'][bp['polynomial']]]
    expected_replacement[hp['polynomial']]=target;require(np['polynomial']==target,'new coefficient output')
  require(replacement==expected_replacement,'all four coefficient substitutions')
 else:
  require(component==[] and replacement=={} and audit['coefficient_splice']=={},'diagnostic has no component splice')
 edits={}
 for rec in hat['extraction']:
  for j,prod in enumerate(rec['products']):
   prefix=rec['side']+'_dot'+str(j)+'_'
   original=next(r for r in hat['source'] if r[0]==prod['high'])
   require(original==[prod['high'],'-',prefix+'high_positive',prefix+'high_negative'],'old high producer')
   edits[prod['high']]=[prod['high'],'-',prefix+'high_hat',rec['half_low_scale']]
 edited=[edits.get(r[0],r) for r in hat['source']]
 reconstructed=edited[:insert]+component+[[n,op,replacement.get(l,l),replacement.get(r,r)] for n,op,l,r in edited[insert:]]
 deps={n:(l,r) for n,op,l,r in reconstructed};live=set();todo=[hat['output']]
 while todo:
  v=todo.pop()
  if type(v)is str and v not in live:live.add(v);todo.extend(deps.get(v,()))
 require(new['source']==[r for r in reconstructed if r[0] in live],'entire independently reconstructed array')
 removed=[r[0] for r in hat['source'] if r[0] not in live]
 require(removed==audit['removed_hat_rows'],'exact old-row removal ledger')
 require(len(removed)==(1344 if structured else 0),'all removed coefficient rows')
 return {'entire_array_reconstructed':True,'external_bindings':binding_record,'five_reused_polynomials':merge_record,
         'old_rows_removed':len(removed),'new_component_rows':len(component),'high_rows_changed':len(edits)}

def run(root,author,artifacts):
 for ext,pin in AUTHOR_PINS.items():require(sha((author/('matrix193_composed_output_scout.'+ext)).read_bytes())==pin,'frozen author '+ext)
 parent_path=artifacts/'matrix193_bounded_high_output.json';require(sha(parent_path.read_bytes())==PARENT_SHA,'parent pin')
 old=read(parent_path);new=read(author/'matrix193_composed_output_scout.json')
 require(len(new['pins'])==11,'eleven author dependencies')
 for name,pin in new['pins'].items():
  location=root if name.startswith('matrix193_balanced_output_scout.') else artifacts
  require(sha((location/name).read_bytes())==pin,'dependency '+name)
 require(sha((author/'matrix193_composed_output_scout.py').read_bytes())==new['source_sha256'],'author self source pin')
 hat=read(artifacts/'matrix193_hat_packing_scout.json');balanced=read(root/'matrix193_balanced_output_scout.json')
 structured=read(artifacts/'matrix193_structured_coefficient_scout.json')['packet']
 answer=[]
 for index,(previous,current) in enumerate(zip(old['packets'],new['packets'])):
  row={'name':current['name'],'ledger':audit_graph(current),'registry':registry_check(current),'exact_algebra':exact_identity(previous,current)}
  row['degree_certificate']=degree_certificate(current,previous)
  row['composition_audit']=composition_check(hat['packets'][index],balanced['packets'][index],structured if index else None,current)
  rng=random.Random(9173+current['n']);numbers=[]
  for mod in [1000000007,1000000009]:
   for j in range(12):
    v={s:rng.randrange(-99,100) for s in current['free']}
    if j<6:v.update(current['fixture_fixed_bindings'])
    x,y=values(current,v,mod),values(previous,v,mod);require(x==y,'independent complete modular comparison');numbers.append([mod,j,x])
  row['complete_modular_comparisons']=numbers;answer.append(row)
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'parent_json_sha256':PARENT_SHA,
         'author_hashes':{ext:sha((author/('matrix193_composed_output_scout.'+ext)).read_bytes()) for ext in ['py','json','md']},
         'dependency_pins':new['pins'],'arrays':answer,'scope':'Full literal graph, exact algebra at one proved Q cut and four fully verified coefficient words; no author execution or native tuple.'}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path);ap.add_argument('--artifacts',type=Path)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);args=ap.parse_args()
 result=run(args.root,args.author_root or args.root,args.artifacts or args.root)
 if args.output:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 else:require(enc(result)==enc(read(args.expect)),'exact receipt')
 print(json.dumps({'status':'PASS','ledgers':[r['ledger'] for r in result['arrays']]}))
