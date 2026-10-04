#!/usr/bin/env python3
"""Independent literal-source and matrix-polynomial audit; no author imports."""
import argparse,json,hashlib
from pathlib import Path
from collections import Counter
AUTH={'py':'e5223ccc69d6c42fff7b5fadfae29fa1d9039d513967f27ed0cb48a8e9fb4bee',
      'json':'a59d1a571695a028d96947d4e2ccd0566af763b272dc170a11d7d1fb92c1c04c',
      'md':'80bdcde5242044365bdcc904d42964c8d083b3a41e894694e438b60da6b51f70'}
def ck(v,m):
 if not v:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def obj(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=obj,parse_constant=bad)
def add(a,b,sgn=1):
 c=a.copy()
 for e,v in b.items():c[e]=c.get(e,0)+sgn*v
 return {e:v for e,v in c.items() if v}
def mul(a,b):
 c={}
 for e,v in a.items():
  for f,w in b.items():c[e+f]=c.get(e+f,0)+v*w
 return {e:v for e,v in c.items() if v}
def pure(packet,Q):
 out={Q:{1:1}}
 for n,op,l,r in packet['source']:
  if n==Q:continue
  if all(type(t)is int or t in out for t in (l,r)):
   a=({0:l} if l else {}) if type(l)is int else out[l]
   b=({0:r} if r else {}) if type(r)is int else out[r]
   out[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
 return out
def mm(a,b):return [sum(a[2*i+k]*b[2*k+j] for k in range(2)) for i in range(2) for j in range(2)]
I=[1,0,0,1]
def word(w,letters):
 v=I
 for s in w:v=mm(v,letters[s])
 return v
def mpadd(*polys):
 out={}
 for p in polys:
  for e,m in p.items():out[e]=[x+y for x,y in zip(out.get(e,[0]*4),m)]
 return {e:m for e,m in out.items() if any(m)}
def mpmul(a,b):
 out={}
 for e,m in a.items():
  for f,n in b.items():out=mpadd(out,{e+f:mm(m,n)})
 return out
def shift(a,k):return {e+k:m for e,m in a.items()}

def structures(parent,p,raw,values):
 letters=raw['packet']['letters'];tiles=raw['packet']['tiles'];C=[-31653619,195915076,-3702035,22913161]
 ck(C[0]*C[3]-C[1]*C[2]==1,'conjugator determinant');CI=[C[3],-C[1],-C[2],C[0]]
 load=word('01010111'*2,letters);ck(load[0]*load[3]-load[1]*load[2]==1,'LOAD word determinant')
 ck(parent['groups'][-2]['kind']=='LOAD' and parent['groups'][-2]['matrix']==[load[3],-load[1],-load[2],load[0]],'exact fixed LOAD inverse')
 words={};co=[]
 for side,kind,port in [('X','K','h'),('Y','G','g')]:
  gs=[g for g in parent['groups'] if g['kind']==kind];words[side]=[]
  for g in gs:
   ws={tiles[e-2][port] for e in g['edges']};ck(len(ws)==1,'one literal word per class');w=next(iter(ws));words[side].append(w)
   M=word(w,letters);M=mm(mm(CI,M),C) if side=='X' else M;ck(M==g['matrix'],'entire grouped word matrix')
  if side=='Y':gs=gs+[parent['groups'][-2]]
  for column in range(2):
   forward=[]
   for g in gs:
    M=g['matrix'];forward.extend([M[column]-int(column==0),M[2+column]-int(column==1)])
   old=parent['extraction'][0 if side=='X' else 1]['products'][column]
   ck(forward==old['coefficients'],'raw grouped matrix coefficients')
   new=p['replacement'][old['polynomial']];want={e:v for e,v in enumerate(reversed(forward)) if v}
   ck(values[new]==want,'all coefficients of literal new output')
   co.append({'side':side,'column':column,'terms':len(want),'degree':max(want),'ascending_sha256':sha(enc(list(reversed(forward))))})
 y=words['Y'];ck(len(y)==96,'Y words');original={'R':{},'L':{}};by_state={}
 for j in range(29):
  ws=y[4+3*j:7+3*j]
  if ws[2].endswith(']'):
   base=ws[0][:-1];ck(ws==[base+'0',base+'1',base+']'],'literal right triple');cat='R'
  else:
   base=ws[0][1:];ck(ws==['0'+base,'1'+base,'['+base],'literal left triple');cat='L'
  ck(len(base)==2 and base[1] in '01','state and scanned symbol')
  original[cat][28-j]=word(base,letters);by_state.setdefault(base[0],{})[base[1]]=(j,cat)
 pairs={s:{} for s in ['RR','LL','RL','LR']};single=[]
 for state,rec in by_state.items():
  if len(rec)==2:
   j0,c0=rec['0'];j1,c1=rec['1'];ck(j1==j0+1,'literal read adjacency');pairs[c0+c1][28-j1]=letters[state]
  else:
   ck(state=='J' and rec=={'0':(18,'L')},'single J0 position');single.append((state,28-rec['0'][0]))
 T0={0:letters['0']};T1={0:letters['1']};V={1:letters['0'],0:letters['1']}
 newR=mpadd(mpmul(pairs['RR'],V),shift(mpmul(pairs['RL'],T0),1),mpmul(pairs['LR'],T1))
 newL=mpadd(mpmul(pairs['LL'],V),mpmul(pairs['RL'],T1),shift(mpmul(pairs['LR'],T0),1),{10:word('J0',letters)})
 ck(newR==original['R'] and newL==original['L'],'ordered noncommuting paired identities')
 saved={cat:[{'exponent':e,'matrix':m} for e,m in sorted(poly.items())] for cat,poly in pairs.items()}
 ck(saved==p['structural_records']['Y']['read_pair_groups'],'all pair records')
 ck(p['structural_records']['Y']['single']==[['J',10]],'single record')
 xleft={s:{} for s in ['0','1']}
 for j in range(22):
  ws=words['X'][4+3*j:7+3*j]
  if ws[2].endswith(']'):continue
  state,bit=ws[0][0],ws[0][-1];ck(ws==[state+'0'+bit,state+'1'+bit,'['+state+'0'+bit],'X left ordering')
  xleft[bit][21-j]=letters[state]
 polys=[xleft['0'],xleft['1'],pairs['RR'],pairs['LL']]
 supports=[{2:1,3:1,13:1,16:1,17:1,18:1},{8:1,9:1,11:1,12:1,14:1,15:1},{0:1,6:1,8:1,25:1,27:1},{13:1,15:1,17:1,21:1,23:1}]
 factored=[add(mul({2:1},mul({0:1,1:1},{0:1,14:1})),mul({13:1},{0:1,5:1})),mul({8:1},mul({0:1,1:1},{0:1,3:1,6:1})),add(mul({6:1,25:1},{0:1,2:1}),{0:1}),mul({13:1},add(mul({0:1,2:1},{8:1,2:1}),{0:1}))]
 for poly,supp,fact,rec in zip(polys,supports,factored,p['trace_two_records']):
  ck(supp==fact and set(poly)==set(supp),'exact support factorization')
  ck(rec['step']==6 and rec['support_indices']==sorted(poly) and rec['matrices']==[poly[e] for e in sorted(poly)],'literal trace record')
  ck(all(M[0]+M[3]==2 for M in poly.values()),'all trace-two coefficients')
  for entry,name in enumerate(rec['outputs']):
   ck(values[name]=={6*e:M[entry] for e,M in poly.items() if M[entry]},'entire trace entry output')
 ck([r['common_lower_left'] for r in p['trace_two_records']]==[-20,5,-20,5],'four common lower-left constants')
 return {'full_word_matrix_groups':168,'coefficient_outputs':co,'pair_counts':{k:len(v) for k,v in pairs.items()},'trace_supports':[sorted(s) for s in supports],'ordered_pair_identities':True}

def whole(parent,p):
 insert=parent['stage_counts']['packing']+63;component=p['coefficient_component'];replacement=p['replacement'];oldnames={r[0] for r in parent['source']}
 ck(len(replacement)==4,'exactly four substitutions')
 ck(all(r[0] not in oldnames for r in component),'fresh component names')
 arr=parent['source'][:insert]+component+[[n,op,replacement.get(l,l),replacement.get(r,r)] for n,op,l,r in parent['source'][insert:]]
 deps={n:(l,r) for n,op,l,r in arr};live=set();todo=[parent['output']]
 while todo:
  v=todo.pop()
  if type(v)is str and v not in live:live.add(v);todo.extend(deps.get(v,()))
 ck([r for r in arr if r[0] in live]==p['source'],'entire literal splice')
 removed=[r[0] for r in parent['source'] if r[0] not in live]
 ck(removed==p['removed_parent_rows'] and len(removed)==633,'all old private rows')
 ck(p['free']==parent['free'] and p['witnesses']==parent['witnesses'] and p['fixed_numerals']==parent['fixed_numerals'],'same supplied interface')
 known=set(p['free']);ct=Counter()
 for n,op,l,r in p['source']:
  ck(n not in known and op in ['+','-','*'] and all(type(v)is int or v in known for v in (l,r)),'full topological audit');known.add(n);ct[op]+=1
 ck(known==live,'all paid rows and free ports live')
 retained=0
 for row in parent['source']:
  if row[0] not in removed:
   ck(all(v not in removed or v in replacement for v in row[2:]),'private cone closure');retained+=1
 ck(retained==1046 and len(component)==578,'retained and inserted counts')
 # Four coefficient outputs have been proved equal independently. Every
 # retained surrounding row has identical syntax after those substitutions.
 d={r[0]:r for r in p['source']}
 for n,op,l,r in parent['source']:
  if n not in removed:ck(d[n]==[n,op,replacement.get(l,l),replacement.get(r,r)],'all surrounding rows literal')
 ck(p['output']==parent['output'],'same final output')
 literals={v for row in p['source'] for v in row[2:] if type(v)is int};cm=Counter(r[1] for r in component)
 ck((len(p['source']),ct['*'],ct['+']+ct['-'],len(p['witnesses']),len(literals))==(1624,791,833,146,137),'complete count')
 ck((cm['*'],cm['+']+cm['-'])==(329,249),'component count')
 return {'total':1624,'M':791,'A':833,'witnesses':146,'literal_count':137,'component':{'M':329,'A':249},'retained_parent_rows':retained,'whole_all_ring_identity':True,'exact_degree_inherited':parent['ledger']['proved_exact_degree']}

def run(root,author):
 for ext,h in AUTH.items():ck(sha((author/('matrix193_entry_shared_coefficient_scout.'+ext)).read_bytes())==h,'author pin '+ext)
 receipt=read(author/'matrix193_entry_shared_coefficient_scout.json')
 for name,h in receipt['pins'].items():ck(sha((root/name).read_bytes())==h,'dependency '+name)
 parent=read(root/'matrix193_composed_output_scout.json')['packets'][1];p=receipt['packet'];raw=read(root/'matrix193_gamma1_recode.json')
 values=pure(p,parent['ports']['Q']);facts=structures(parent,p,raw,values);ledger=whole(parent,p)
 ck(parent['ledger']['proved_exact_degree']==p['ledger']['degree']==35587,'identity degree transfer')
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'author_pins':AUTH,'dependency_pins':receipt['pins'],'structural_audit':facts,'whole_source_audit':ledger,'scope':'Exact literal source and coefficient proof; no author or predecessor code imported/executed; no native fixture.'}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=run(a.root,a.author_root or a.root)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(enc(r)==enc(read(a.expect)),'exact typed receipt')
 print('PASS: paired matrix identities, four complete coefficients, full1624 source and146w')
