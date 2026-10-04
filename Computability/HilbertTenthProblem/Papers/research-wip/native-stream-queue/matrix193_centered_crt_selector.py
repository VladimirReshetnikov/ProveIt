#!/usr/bin/env python3
"""Complete centered CRT selectors; standalone pinned-data research CLI."""
import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

PINS={
 'matrix193_crt_selector.py':'eb2449443cb61ee7b158d2727a15bc94d83b41c56a20a53bbc8072a3510409b6',
 'matrix193_crt_selector.json':'7c2c1f5330838eb942fb36a15961920f079cd4fd2a306732ca9d8ae589383455',
 'matrix193_crt_selector.md':'3e8e8323f98712db79d791c80e0f8acf1f859231fbf80f02742fab6dd44d733c',
 'matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742',
 'matrix193_context_absorption.md':'d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b',
 'matrix193_synchronized_rows.md':'ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2',
}
COLS=['K0','K1','K2','G0','G1','G2']
STATES=['x0','x1','y0','y1','next_x0','next_x1','next_y0','next_y1']
CONSTS=['L','m_bias','T_squared']+['center_'+c for c in COLS]

THREE_SQUARE_FIXTURES={"0": {"G0": [64, 11875511289165781362212097773750, 917751692813122880649491055329], "G1": [840, 9602658856048490901093001785375, 7046912759721008435183700979186], "G2": [28, 11909012212032323053546564141726, 213224488345656111245668672231], "K0": [122, 10900720596676901804037122885617, 4800450710292609843818891159488], "K1": [58, 10030194257753665441864400961527, 6423802588848021170881646095172], "K2": [172, 11752094692053101203687567913014, 1938635318408604636346241060279]}, "95": {"G0": [74, 11000154816231720199190351178640, 4568000718881222010201212490671], "G1": [198, 8878843530726414849203708571196, 7939532360639571232430022817449], "G2": [202, 8878909808989009960178517492454, 7939458240497522367794244238351], "K0": [336, 9347942535007122627780806603790, 7381463737699310882272253737231], "K1": [208, 10854470440868639474238960554276, 4904131727133176677574549227291], "K2": [110, 11906969283881079157222387188364, 306788235559599074379440573255]}}

def need(ok,msg):
 if not ok:raise ValueError(msg)

def sha(b):return hashlib.sha256(b).hexdigest()

def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def read_json(path):
 def pairs(items):
  out={}
  for k,v in items:need(k not in out,'duplicate key');out[k]=v
  return out
 def bad(v):raise ValueError('noninteger JSON number '+v)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)

# Exact sparse polynomial ring; monomials are sorted tuples of variable names.
def pc(n):return {():n} if n else {}
def pv(s):return {(s,):1}
def add(a,b,sign=1):
 out=a.copy()
 for k,v in b.items():
  out[k]=out.get(k,0)+sign*v
  if not out[k]:del out[k]
 return out

def mul(a,b):
 out={}
 for x,v in a.items():
  for y,w in b.items():
   k=tuple(sorted(x+y));out[k]=out.get(k,0)+v*w
 return {k:v for k,v in out.items() if v}

def sq(a):return mul(a,a)
def psum(xs):
 out={}
 for x in xs:out=add(out,x)
 return out

def phash(p):
 h=hashlib.sha256()
 for k,v in sorted(p.items()):h.update(json.dumps([k,hex(v)],separators=(',',':')).encode()+b'\n')
 return h.hexdigest()

def pdegree(p,ports):return max((sum(x in ports for x in k) for k in p),default=-1)

class Build:
 def __init__(self):self.rows=[]
 def op(self,op,a,b):
  out='r'+str(len(self.rows));self.rows.append([out,op,a,b]);return out
 def add(self,a,b):return self.op('+',a,b)
 def sub(self,a,b):return self.op('-',a,b)
 def mul(self,a,b):return self.op('*',a,b)
 def sos(self,args):
  terms=[self.mul(a,a) for a in args];out=terms[0]
  for a in terms[1:]:out=self.add(out,a)
  return out

def auxiliaries(mode):
 out=['z']+['bound_z_0']
 for c in COLS:
  out+=['q_'+c]+(['a_'+c] if mode=='supplied' else [])+['bound_'+c+'_'+str(i) for i in range(3)]
 return out

def audit_packet(packet,constants):
 ports=packet['ports'];seen=set(ports)|set(constants);by={};M=0;degrees={p:1 for p in ports}|{p:0 for p in constants}
 def known(x):return type(x) is int or (type(x) is str and x in seen)
 def deg(x):return 0 if type(x) is int else degrees[x]
 for row in packet['instructions']:
  need(type(row) is list and len(row)==4,'row')
  out,op,a,b=row;need(type(out) is str and out not in seen and op in ['+','-','*'] and known(a) and known(b),'closure')
  degrees[out]=deg(a)+deg(b) if op=='*' else max(deg(a),deg(b));M+=op=='*';seen.add(out);by[out]=row
 need(packet['output'] in by,'output')
 live=set();stack=[packet['output']]
 while stack:
  v=stack.pop()
  if v in live:continue
  live.add(v)
  if v in by:
   stack.extend(a for a in by[v][2:] if type(a) is str)
 need(set(by)<=live and set(ports)<=live and set(constants)<=live,'liveness')
 ledger={'M':M,'A':len(by)-M,'total':len(by)}
 return ledger,degrees[packet['output']]

def emit(mode,countdown,parent):
 b=Build();m=b.add(b.mul('L','z'),'m_bias')
 residuals=[b.sub(b.sos(['z']+['bound_z_0']),5928325)]
 coeff={};quotient_residuals=[]
 for c in COLS:
  rem=b.sub('center_'+c,b.mul(m,'q_'+c))
  a='a_'+c if mode=='supplied' else rem;coeff[c]=a
  if mode=='supplied':
   eq=b.sub(rem,a);residuals.append(eq);quotient_residuals.append(eq)
  residuals.append(b.sub(b.sos([a]+['bound_'+c+'_'+str(i) for i in range(3)]),'T_squared'))
 for f,u,v,p,q in [('K','x0','x1','next_x0','next_x1'),('G','y0','y1','next_y0','next_y1')]:
  residuals.append(b.sub(b.add(p,p),b.add(b.mul(coeff[f+'0'],u),b.mul(coeff[f+'2'],v))))
  residuals.append(b.sub(b.sub(b.mul(coeff[f+'0'],q),b.mul(coeff[f+'1'],p)),b.add(v,v)))
 out=b.sos(residuals);sync_output=out;sync_rows=len(b.rows)
 if countdown:
  old=parent['variants']['computed_countdown'];oldsync=parent['variants']['computed_synchronized'];rename={oldsync['output']:out}
  tail=old['instructions'][len(oldsync['instructions']):];need(len(tail)==26,'wrapper size')
  for name,op,a,c in tail:rename[name]=b.op(op,rename.get(a,a),rename.get(c,c))
  out=rename[old['output']]
 packet={'mode':mode,'countdown':countdown,'domain':'All state and auxiliary coordinates are signed integers. The polynomial is globally real nonnegative; real transition exactness fails.','ports':STATES+(['n','next_n'] if countdown else [])+auxiliaries(mode),'auxiliary_witnesses':len(auxiliaries(mode)),'instructions':b.rows,'output':out,'sync_output':sync_output,'sync_rows':sync_rows,'residual_wires':residuals,'quotient_residual_wires':quotient_residuals,'coefficient_wires':coeff,'m_wire':m}
 packet['ledger'],packet['degree_upper']=audit_packet(packet,CONSTS)
 expected={('supplied',False):(58,67,4),('supplied',True):(70,81,6),('computed',False):(52,55,8),('computed',True):(64,69,10)}[mode,countdown]
 need((packet['ledger']['M'],packet['ledger']['A'],packet['degree_upper'])==expected,'paid ledger/degree')
 need(packet['auxiliary_witnesses']==(32 if mode=='supplied' else 26),'auxiliary count')
 return packet

def source_poly(packet,substitutions=None):
 env={x:pv(x) for x in packet['ports']+CONSTS};env.update(substitutions or {})
 def val(x):return pc(x) if type(x) is int else env[x]
 for out,op,a,b in packet['instructions']:
  A=val(a);B=val(b);env[out]=mul(A,B) if op=='*' else add(A,B,1 if op=='+' else -1)
 return env

def direct_poly(mode,countdown):
 V=pv;m=add(mul(V('L'),V('z')),V('m_bias'))
 triples=lambda prefix:psum([sq(V(prefix+'_'+str(i))) for i in range(3)])
 rs=[add(add(sq(V('z')),sq(V('bound_z_0'))),pc(5928325),-1)];rem={};co={}
 for c in COLS:
  rem[c]=add(V('center_'+c),mul(m,V('q_'+c)),-1);a=V('a_'+c) if mode=='supplied' else rem[c];co[c]=a
  if mode=='supplied':rs.append(add(rem[c],a,-1))
  rs.append(add(add(sq(a),triples('bound_'+c)),V('T_squared'),-1))
 for f,u,v,p,q in [('K','x0','x1','next_x0','next_x1'),('G','y0','y1','next_y0','next_y1')]:
  rs.append(add(mul(pc(2),V(p)),add(mul(co[f+'0'],V(u)),mul(co[f+'2'],V(v))),-1))
  rs.append(add(add(mul(co[f+'0'],V(q)),mul(co[f+'1'],V(p)),-1),mul(pc(2),V(v)),-1))
 U=psum([sq(r) for r in rs]);out=U
 if countdown:
  load=[add(V('next_x0'),V('x0'),-1),add(V('next_x1'),V('x1'),-1),add(V('next_y0'),add(mul(pc(52891),V('y0')),mul(pc(94920),V('y1'))),-1),add(V('next_y1'),add(mul(pc(-29036),V('y0')),mul(pc(-52109),V('y1'))),-1),add(add(V('next_n'),V('n'),-1),pc(1))]
  out=mul(psum([sq(r) for r in load]),add(U,add(sq(V('n')),sq(V('next_n')))))
 return out,rs,rem

def evaluate(packet,constants,ports,modulus=None):
 env=constants|ports
 def val(x):return x if type(x) is int else env[x]
 for out,op,a,b in packet['instructions']:
  A=val(a);B=val(b);v=A*B if op=='*' else A+B if op=='+' else A-B
  env[out]=v if modulus is None else v%modulus
 return env

def direct_numeric(mode,countdown,constants,ports):
 e=constants|ports;z=e['z'];m=e['L']*z+e['m_bias']
 triples=lambda prefix:sum(e[prefix+'_'+str(i)]**2 for i in range(3))
 rs=[z*z+e['bound_z_0']**2-5928325];co={}
 for c in COLS:
  rem=e['center_'+c]-m*e['q_'+c];a=e['a_'+c] if mode=='supplied' else rem;co[c]=a
  if mode=='supplied':rs.append(rem-a)
  rs.append(a*a+triples('bound_'+c)-e['T_squared'])
 for f,u,v,p,q in [('K','x0','x1','next_x0','next_x1'),('G','y0','y1','next_y0','next_y1')]:
  rs.extend([2*e[p]-co[f+'0']*e[u]-co[f+'2']*e[v],co[f+'0']*e[q]-co[f+'1']*e[p]-2*e[v]])
 U=sum(r*r for r in rs)
 if not countdown:return U
 load=(e['next_x0']-e['x0'])**2+(e['next_x1']-e['x1'])**2+(e['next_y0']-52891*e['y0']-94920*e['y1'])**2+(e['next_y1']+29036*e['y0']+52109*e['y1'])**2+(e['next_n']-e['n']+1)**2
 return load*(U+e['n']**2+e['next_n']**2)

def degree_line(packet,constants):
 env={p:{} for p in packet['ports']}|{k:pc(v) for k,v in constants.items()};env['z']=pv('t')
 if packet['mode']=='computed':env['q_K0']=pv('t')
 if packet['countdown']:env['n']=pv('t')
 out=source_poly(packet,env)[packet['output']];degree=pdegree(out,{'t'})
 expected=(8 if packet['mode']=='computed' else 4)+(2 if packet['countdown'] else 0)
 need(degree==expected,'exact degree line');leader=out[('t',)*degree]
 need(leader==(constants['L']**4 if packet['mode']=='computed' else 1),'degree leader')
 return {'exact_degree':degree,'specialization':'all state and square-root ports zero; z=t; additionally q_K0=t in computed mode, n=t in countdown mode','coefficient_terms':len(out),'polynomial_sha256':phash(out),'leading_coefficient_hex':hex(leader)}

def selector_certificates():
 certs={};circle_rhs=5928325;radius=math.isqrt(circle_rhs)
 for z in range(-radius,radius+1):
  n=circle_rhs-z*z;y=math.isqrt(n)
  if y*y==n:certs[z]=[y]
 need(len(certs)==96 and min(certs)==-radius and max(certs)==radius,'exact circle selector labels')
 return certs


def actual_zero_checks(variants,constants,table,labels,moduli,T,selector_certs):
 checks=wrong=loader=aliases=0
 for index in (0,95):
  label=next(r['label'] for r in labels if r['table_index']==index and r['canonical']);i=next(j for j,r in enumerate(labels) if r['label']==label);row=table[index]
  roots_by_col=THREE_SQUARE_FIXTURES[str(index)]
  for packet in variants.values():
   ports={p:0 for p in packet['ports']};ports['z']=label
   ports.update({'bound_z_'+str(j):a for j,a in enumerate(selector_certs[label])})
   for c in COLS:
    a=2*row[c[0]][int(c[1])];roots=roots_by_col[c]
    need(len(roots)==3 and all(type(v) is int for v in roots) and sum(v*v for v in roots)==T*T-a*a,'actual three-square certificate')
    q,r=divmod(constants['center_'+c]-a,moduli[i]);need(r==0,'actual quotient');ports['q_'+c]=q
    if packet['mode']=='supplied':ports['a_'+c]=a
    ports.update({'bound_'+c+'_'+str(j):v for j,v in enumerate(roots)})
   for f,u,v,a,b in [('K',2,-1,'x','next_x'),('G',-3,4,'y','next_y')]:
    M=table[index][f];ports[a+'0']=u;ports[a+'1']=v;ports[b+'0']=u*M[0]+v*M[2];ports[b+'1']=u*M[1]+v*M[3]
   need(evaluate(packet,constants,ports)[packet['output']]==0,'full integer tile zero');checks+=1
   ports['next_x1']+=1;need(evaluate(packet,constants,ports)[packet['output']]>0,'wrong row rejected');wrong+=1
 for packet in variants.values():
  if packet['countdown']:
   for counter in [-2,3]:
    ports={p:(j%7)-3 for j,p in enumerate(packet['ports'])}
    ports.update({'x0':2,'x1':-1,'next_x0':2,'next_x1':-1,'y0':-3,'y1':4,'next_y0':-3*52891+4*94920,'next_y1':3*29036-4*52109,'n':counter,'next_n':counter-1})
    need(evaluate(packet,constants,ports)[packet['output']]==0,'LOAD leaves CRT auxiliaries unrestricted');loader+=1
  ports={p:0 for p in packet['ports']};ports.update({'z':-2434,'bound_z_0':63,'x0':1,'y0':1})
  for c in COLS:
   ports['q_'+c]=Fraction(constants['center_'+c],moduli[0]);ports['bound_'+c+'_0']=T
  need(any(ports['q_'+c].denominator!=1 for c in COLS),'noninteger alias quotient')
  need(evaluate(packet,constants,ports)[packet['output']]==0,'explicit rational alias');aliases+=1
 return {'full_integer_tile_zeros':checks,'wrong_state_rejections':wrong,'integer_loader_zeros_with_unconstrained_CRT_auxiliaries':loader,'explicit_rational_false_transition_zeros':aliases,'actual_three_square_certificates':THREE_SQUARE_FIXTURES,'scope':'Two actual nodes in all four complete arrays, with exact integer square decompositions checked directly. Rational aliases map both nonzero current rows to zero, impossible for an invertible tile. No primality assertion is used.'}
def positive_history(h,local,parent,constants):
 b=Build();inverse={};positive_ports=[]
 for step in range(h):
  for name in ['next_x0','next_x1','next_y0','next_y1','next_n']+auxiliaries('computed'):
   key='s'+str(step)+'_'+name;pos='positive_'+key;positive_ports.append(pos);inverse[key]=b.sub(pos,'offset')
 initial=parent['initial_state'];state={'x0':initial['X'][0],'x1':initial['X'][1],'y0':initial['Y'][0],'y1':initial['Y'][1],'n':'ordinary_x'};outs=[];step_maps=[]
 for step in range(h):
  rename=state.copy()
  rename.update({p:inverse['s'+str(step)+'_'+p] for p in ['next_x0','next_x1','next_y0','next_y1','next_n']+auxiliaries('computed')})
  step_maps.append(rename.copy())
  for out,op,a,c in local['instructions']:rename[out]=b.op(op,rename.get(a,a),rename.get(c,c))
  outs.append(rename[local['output']]);state={p:rename['next_'+p] for p in ['x0','x1','y0','y1','n']}
 rename=state.copy();endpoint=parent['endpoint']
 for out,op,a,c in endpoint['instructions']:rename[out]=b.op(op,rename.get(a,a),rename.get(c,c))
 total=rename[endpoint['output']]
 for out in outs:total=b.add(total,out)
 packet={'duration':h,'domain':'ordinary_x is natural; all listed witness ports are positive integers','witness_ports':['offset']+positive_ports,'ports':['ordinary_x','offset']+positive_ports,'instructions':b.rows,'output':total,'state_reconstruction_rows':31*h,'local_instances':h,'endpoint_rows':7,'final_joins':h,'source_composition':'Copy the full133-row computed countdown at each step after31 shared coordinate subtractions, then the unchanged7-row endpoint and h joins.'}
 packet['ledger'],packet['degree_upper']=audit_packet(packet,CONSTS)
 need(packet['ledger']['total']==165*h+7 and len(packet['witness_ports'])==31*h+1 and packet['degree_upper']<=10,'positive history ledger')
 for seed in range(6):
  ports={p:1+(j+seed)%7 for j,p in enumerate(positive_ports)}|{'offset':3+seed,'ordinary_x':seed}
  env=evaluate(packet,constants,ports);direct=0
  for mapping in step_maps:
   localports={p:(v if type(v) is int else env[v]) for p,v in mapping.items()}
   direct+=direct_numeric('computed',True,constants,localports)
  final={p:(v if type(v) is int else env[v]) for p,v in state.items()}
  direct+=(final['x0']-final['y0'])**2+(final['x1']-final['y1'])**2+final['n']**2
  need(env[total]==direct,'full positive history composition')
 packet['full_composition_checks']=6
 return packet

def difference_prime_support(labels):
 support=set();differences={a-b for i,a in enumerate(labels) for b in labels[:i]}
 for delta in differences:
  n=delta;p=2
  while p*p<=n:
   if n%p==0:
    support.add(p)
    while n%p==0:n//=p
   p+=1
  if n>1:support.add(n)
 L0=math.prod(support)
 for delta in differences:
  rem=delta
  for p in support:
   while rem%p==0:rem//=p
  need(rem==1,'difference prime support')
 return sorted(support),len(differences),L0

def make(root):
 for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'pin '+name)
 parent=read_json(root/'matrix193_crt_selector.json');need(parent['source_sha256']==PINS['matrix193_crt_selector.py'],'parent self source')
 table=parent['transition_table'];need(type(table) is list and len(table)==96,'table');ids=[]
 for row in table:
  need(type(row['tile_id']) is int,'tile id');ids.append(row['tile_id'])
  for f in ['K','G']:
   a=row[f];need(type(a) is list and len(a)==4 and all(type(x) is int for x in a),'matrix')
   need(a[0]*a[3]-a[1]*a[2]==1 and a[0]!=0 and a[0]%5==1,'unimodular Gamma1 pivot')
 need(len(set(ids))==96,'distinct tiles')
 selector_certs=selector_certificates();zs=sorted(selector_certs)
 labels=[{'label':z,'table_index':i,'tile_id':ids[i],'canonical':True,'circle_witness':selector_certs[z][0]} for i,z in enumerate(zs)]
 need(len(labels)==96 and {r['table_index'] for r in labels}==set(range(96)),'surjective labels')
 support,difference_count,L0=difference_prime_support(zs)
 need(len(support)==148 and L0.bit_length()==1221,'fixture radical size')
 values={c:[table[r['table_index']][c[0]][int(c[1])] for r in labels] for c in COLS}
 T=2*max(abs(v) for col in values.values() for v in col)+1
 L=L0*max(1,(2*T+1+L0-1)//L0);moduli=[1+(z+2435)*L for z in zs];product=math.prod(moduli)
 need(T%2==1 and 2*T<min(moduli),'centered range')
 need(all(math.gcd(m,n)==1 for i,m in enumerate(moduli) for n in moduli[:i]),'pairwise coprime')
 constants={'L':L,'m_bias':2435*L+1,'T_squared':T*T};quotients={};compiled={};node_checks=0
 partial=[product//m for m in moduli];inverses=[pow(p,-1,m) for p,m in zip(partial,moduli)]
 for c in COLS:
  C=sum((2*v+T)*p*inv for v,p,inv in zip(values[c],partial,inverses))%product
  compiled[c]=C;constants['center_'+c]=C-T;quotients[c]=[]
  for m,v in zip(moduli,values[c]):
   A=2*v;residue=A+T;need(0<residue<2*T<m and C%m==residue,'CRT match')
   gap=T*T-A*A;need(gap>0 and gap%8 in (1,5),'Legendre coefficient hypothesis')
   q,r=divmod(constants['center_'+c]-A,m);need(r==0,'integer quotient');quotients[c].append(q);node_checks+=1
 fixed={k:{'hex':hex(v),'bit_length':abs(v).bit_length(),'sha256_hex':sha(hex(v).encode())} for k,v in constants.items()}
 variants={};rings={};formal_terms=0;comparisons=0;modular_checks=0
 for mode in ['supplied','computed']:
  for count in [False,True]:
   name=mode+('_countdown' if count else '_synchronized');packet=emit(mode,count,parent)
   env=source_poly(packet);formula,rs,_=direct_poly(mode,count)
   need(env[packet['output']]==formula,'whole formal polynomial')
   need([env[r] for r in packet['residual_wires']]==rs,'all formal residuals')
   need(pdegree(formula,set(packet['ports']))==packet['degree_upper'],'weighted exact degree')
   packet['formal_identity']={'terms':len(formula),'sha256':phash(formula),'residual_terms':[len(r) for r in rs],'constants_are_independent_formal_ports':True};formal_terms+=len(formula)
   packet['degree_certificate']=degree_line(packet,constants)
   for seed in range(12):
    ports={p:((seed+3)*(i+7)%23)-11 for i,p in enumerate(packet['ports'])}
    if seed>=8:ports={p:Fraction(v,((i+seed)%3)+1) for i,(p,v) in enumerate(ports.items())}
    result=evaluate(packet,constants,ports)[packet['output']]
    need(result==direct_numeric(mode,count,constants,ports),'full signed/rational reference');comparisons+=1
    if seed<8:
     for prime in (1000000007,1000000009):
      need(evaluate(packet,constants,ports,prime)[packet['output']]==result%prime,'modular source');modular_checks+=1
   variants[name]=packet;rings[name]=formula
 pullbacks=[]
 for count in [False,True]:
  suffix='_countdown' if count else '_synchronized';supplied=variants['supplied'+suffix]
  _,_,rem=direct_poly('computed',count);mapped=source_poly(supplied,{'a_'+c:rem[c] for c in COLS})
  need(mapped[supplied['output']]==rings['computed'+suffix],'whole centered pullback')
  need(all(mapped[r]=={} for r in supplied['quotient_residual_wires']),'quotient residual vanishes')
  pullbacks.append({'countdown':count,'coefficient_terms':len(rings['computed'+suffix]),'sha256':phash(rings['computed'+suffix])})
 node_actions=0
 for i,record in enumerate(labels):
  row=table[record['table_index']];got={c:constants['center_'+c]-moduli[i]*quotients[c][i] for c in COLS}
  for family in ['K','G']:
   a,b,c,d=row[family]
   for u,v in [(0,0),(1,0),(-2,3),(Fraction(2,3),Fraction(-5,7))]:
    p=a*u+c*v;q=b*u+d*v
    need(2*p-got[family+'0']*u-got[family+'2']*v==0,'scaled row0')
    need(got[family+'0']*q-got[family+'1']*p-2*v==0,'scaled row1');node_actions+=1
 zeros=actual_zero_checks(variants,constants,table,labels,moduli,T,selector_certs)
 positive={str(h):positive_history(h,variants['computed_countdown'],parent,constants) for h in [1,2]}
 endpoint=parent['endpoint'];need(endpoint['ledger']=={'M':3,'A':4,'total':7},'endpoint ledger')
 return {'schema':'matrix193-centered-crt-selector-v1','status':'PASS_COMPLETE_INTEGER_LOCAL_RELATIONS','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'predecessor_code_executed':False,'transition_table':table,'selector_labels':labels,'selector_circle':{'floor_radius':2434,'circle_rhs':5928325,'scanned_integer_labels':4869,'admissible_labels':96,'canonical_labels':96,'duplicate_labels':0,'proof':'For integer z and b, z^2+b^2=5928325 implies |z|<=2434; the complete finite integer-square scan saves a witness for every admissible label.'},'fixed_numeral_recipe':{'L0':'product of the distinct primes dividing differences of the96 admissible selector labels','difference_primes':support,'distinct_differences':difference_count,'L0_bit_length':L0.bit_length(),'L':'L0*max(1,ceil((2T+1)/L0)); actual fixture uses L=L0','T':T,'T_recipe':'2*maximum absolute value of the six retained actual columns +1','moduli':moduli,'modulus_formula':'1+(z+2435)L','common_product_bits':product.bit_length(),'CRT':'For each column c: C_c=sum_i (2*entry_i+T)*(M/m_i)*inverse(M/m_i mod m_i), reduced modulo M=product_i m_i; bound fixed numeral center_c=C_c-T. All operations are fixed-data compilation.','fixed_numerals':fixed,'node_coefficient_checks':node_checks,'pairwise_gcd_checks':96*95//2,'maximum_fixed_numeral_bits':max(abs(v).bit_length() for v in constants.values())},'variants':variants,'full_polynomial_pullbacks':pullbacks,'finite_checks':{'complete_signed_rational_source_comparisons':comparisons,'including_rational':16,'modular_comparisons':modular_checks,'exact_row_actions':node_actions,'formal_coefficient_entries':formal_terms,'full_integer_and_domain_checks':zeros},'positive_fixed_duration_sources':positive,'uniform_context_extension':{'scope':'Any inherited fixed contexts, with all paired actions in Hprime subset Gamma1(5); pivots are1 mod5 and cannot vanish. The numeric arrays here remain the selected fixture.','L_recipe':'The same fixed label radical L0, multiplied by max(1,ceil((2T+1)/L0)), with odd T=2*max absolute retained entry+1.','countdown_operations':133,'signed_auxiliary_witnesses':26},'initial_state':parent['initial_state'],'endpoint':endpoint,'fixed_duration_bounds':{'computed_countdown':{'operations':'134h+7','signed_witnesses':'31h','degree_upper':10},'supplied_countdown':{'operations':'152h+7','signed_witnesses':'37h','degree_upper':6},'computed_synchronized':{'operations':'108h+5','signed_witnesses':'30h','degree_upper':8},'positive_computed_countdown':{'operations':'165h+7','positive_witnesses':'31h+1','degree_upper':10}},'scope':'Exact signed-integer local and fixed-duration predicates. SOS is globally real nonnegative, but real transition exactness fails. Unbounded duration packing remains unpaid. The fixed-duration positive-coordinate conversion is paid explicitly.'}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--expect',type=Path);g.add_argument('--output',type=Path);a=p.parse_args();r=make(a.root)
 if a.output:
  with a.output.open('x') as f:json.dump(r,f,indent=2,sort_keys=True);f.write('\n')
 else:need(exact(r,read_json(a.expect)),'exact receipt')
 print('PASS: centered CRT circle selectors107/133 and125/151; full arrays, identities, exact numeral compilation and paid positive fixed durations')

if __name__=='__main__':main()
