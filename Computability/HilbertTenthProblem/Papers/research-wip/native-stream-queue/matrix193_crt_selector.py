#!/usr/bin/env python3
"""Complete finite CRT matrix selectors; standalone pinned-data research CLI."""
import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

PINS={
 'matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742',
 'matrix193_context_absorption.md':'d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b',
 'matrix193_synchronized_rows.md':'ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2',
 'matrix193_unimodular_selector.py':'34c98040cf2d20d88fbfdfe7e71ae88d6904547a5ab8102c0805c71d6bccc456',
 'matrix193_unimodular_selector.json':'c03bc63e10398bb53e19fd1ad6f755fa132164379dce10c523de3ea0dd598e1c',
 'matrix193_unimodular_selector.md':'87ee28420daa8d722b495137a9e76b316a74e95c64c94f656f592849f06640b2',
}
COLS=['K0','K1','K2','G0','G1','G2']
STATES=['x0','x1','y0','y1','next_x0','next_x1','next_y0','next_y1']
CONSTS=['L','T']+['C_'+c for c in COLS]

FOUR_SQUARE_FIXTURES={'node_fixtures': [{'index': 0, 'bounds': {'K0': [79096452, 47805212, 2238780041188960665162722778270477031182995547071166670083724414692853073976986834415999272, 945390377243608492864779734760855957112032282024022571361905577778576961867295307922998588], 'K1': [8342554, 10683266, 2400592245117692153511144853068079490941139587763365318021819321585987631028167683712553428, 378226667932395544696731219314383936399861289765550973782024029736625890866837352715250238], 'K2': [9402652, 101518164, 2413147167623139257666985368953035380458205437045437780727501080839443389264201429678592200, 287437025793269166502528806768358796338440221461146825253930027768738663484690609581230668], 'G0': [476730096, 235223952, 2428544861806563893042158737782648281472342059403979909596126575644278099480630628954586000, 89825228077386844851424284420936983837660552624281387910406901518655890813886845548206496], 'G1': [38688638, 2104506, 1741701064178432400082012921189093843333436699020814971577948513950106753116844498880477798, 1694808579292197059610956639299338626201717178220862721520479428823624996998135956534648300], 'G2': [94186804, 90451988, 2042159091102016122358507184449453694868771963037587360124139100828422121763938820817937052, 1317378064200788161612123125543229158105030413194140354856498353230885139802328005840538520]}}, {'index': 95, 'bounds': {'K0': [5559657984, 16637650432, 19144493129661690285988944691405573369853481836661645538909679374516628523311663758071966720, 14158201145577654821700620570183522360443002951949501710830447375293664389747620031663556096], 'K1': [20866697, 16442471, 21722344354849806161282499207946555716061862512375221480990012216214227576308306522547915693, 9752232185524084761111724359390772482022551101308822031831256099920186660285265020293601710], 'K2': [10787766, 59531298, 23754089361025331125851951666936401260369767721020033712857659117190448088446510412724068750, 1646060599837193289845475827314740012517614280602880498359586448639170973769606825285992812], 'G0': [93467988, 122743172, 23716903632603856786963307140375770477606732915555262321525293365467309740048877466054632792, 2115362605456273242362799620399017891661263488886882279831881945281049340713267865399622028], 'G1': [83954244, 66471540, 16945789497077093505889848480077027903287692772135249261985773935126949199751993785599861612, 16727417469278766024320352789950328397195343302077988909778208373754074382432127181065993272], 'G2': [7620939, 23113353, 21938018066881588400051748557051612871783301727511946414060831386674642287579116613531363550, 9256869890408840870086439538252774400689855798256269534276909483460504695878027760606839807]}}], 'rational_alias_bound': [3771993, 21863463, 2317163858876206560367199083998476254223082147942333577523477678231693937539277952387791070, 732564241907761868566205999577834291082172767326514198247686043726608376997800340607975939]}

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
 out=['z']+['bound_z_'+str(i) for i in range(4)]
 for c in COLS:
  out+=['q_'+c]+(['v_'+c] if mode=='supplied' else [])+['bound_'+c+'_'+str(i) for i in range(4)]
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
 b=Build();h=b.mul('L',b.add('z',1));m=b.add(h,1)
 domain=b.sub(b.mul('z',b.sub(95,'z')),b.sos(['bound_z_'+str(i) for i in range(4)]))
 residuals=[domain];values={};coeff={};quotient_residuals=[]
 for c in COLS:
  rem=b.sub('C_'+c,b.mul(m,'q_'+c))
  v='v_'+c if mode=='supplied' else rem;values[c]=v
  if mode=='supplied':
   eq=b.sub(rem,v);residuals.append(eq);quotient_residuals.append(eq)
  residuals.append(b.sub(b.mul(v,b.sub(h,v)),b.sos(['bound_'+c+'_'+str(i) for i in range(4)])))
  coeff[c]=b.sub(v,'T')
 for family,a,b0,p,q in [('K','x0','x1','next_x0','next_x1'),('G','y0','y1','next_y0','next_y1')]:
  residuals.append(b.sub(p,b.add(b.mul(coeff[family+'0'],a),b.mul(coeff[family+'2'],b0))))
  residuals.append(b.sub(b.sub(b.mul(coeff[family+'0'],q),b.mul(coeff[family+'1'],p)),b0))
 out=b.sos(residuals);sync_output=out;sync_rows=len(b.rows)
 if countdown:
  old=parent['variants']['real_countdown'];oldsync=parent['variants']['real_synchronized'];rename={oldsync['output']:out}
  tail=old['instructions'][len(oldsync['instructions']):];need(len(tail)==26,'wrapper size')
  for name,op,a,c in tail:rename[name]=b.op(op,rename.get(a,a),rename.get(c,c))
  out=rename[old['output']]
 packet={'mode':mode,'countdown':countdown,'domain':'all supplied state and auxiliary coordinates are signed integers; polynomial is nonnegative on all real ports, without real transition exactness','ports':STATES+(['n','next_n'] if countdown else [])+auxiliaries(mode),'auxiliary_witnesses':len(auxiliaries(mode)),'instructions':b.rows,'output':out,'sync_output':sync_output,'sync_rows':sync_rows,'residual_wires':residuals,'quotient_residual_wires':quotient_residuals,'remainder_wires':values,'coefficient_wires':coeff,'h_wire':h,'m_wire':m}
 packet['ledger'],packet['degree_upper']=audit_packet(packet,CONSTS)
 expected={('supplied',False):(67,79,4),('supplied',True):(79,93,6),('computed',False):(61,67,8),('computed',True):(73,81,10)}[mode,countdown]
 need((packet['ledger']['M'],packet['ledger']['A'],packet['degree_upper'])==expected,'paid ledger/degree')
 return packet

def source_poly(packet,substitutions=None):
 env={x:pv(x) for x in packet['ports']+CONSTS};env.update(substitutions or {})
 def val(x):return pc(x) if type(x) is int else env[x]
 for out,op,a,b in packet['instructions']:
  A=val(a);B=val(b);env[out]=mul(A,B) if op=='*' else add(A,B,1 if op=='+' else -1)
 return env

def direct_poly(mode,countdown):
 V=pv;h=mul(V('L'),add(V('z'),pc(1)));m=add(h,pc(1))
 fours=lambda prefix:psum([sq(V(prefix+'_'+str(i))) for i in range(4)])
 rs=[add(mul(V('z'),add(pc(95),V('z'),-1)),fours('bound_z'),-1)];rem={};co={}
 for c in COLS:
  rem[c]=add(V('C_'+c),mul(m,V('q_'+c)),-1);v=V('v_'+c) if mode=='supplied' else rem[c]
  if mode=='supplied':rs.append(add(rem[c],v,-1))
  rs.append(add(mul(v,add(h,v,-1)),fours('bound_'+c),-1));co[c]=add(v,V('T'),-1)
 for f,a,b,p,q in [('K','x0','x1','next_x0','next_x1'),('G','y0','y1','next_y0','next_y1')]:
  rs.append(add(V(p),add(mul(co[f+'0'],V(a)),mul(co[f+'2'],V(b))),-1))
  rs.append(add(add(mul(co[f+'0'],V(q)),mul(co[f+'1'],V(p)),-1),V(b),-1))
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
 e=constants|ports;z=e['z'];h=e['L']*(z+1);m=h+1
 fours=lambda prefix:sum(e[prefix+'_'+str(i)]**2 for i in range(4))
 rs=[z*(95-z)-fours('bound_z')];co={}
 for c in COLS:
  rem=e['C_'+c]-m*e['q_'+c];v=e['v_'+c] if mode=='supplied' else rem
  if mode=='supplied':rs.append(rem-v)
  rs.append(v*(h-v)-fours('bound_'+c));co[c]=v-e['T']
 for f,a,b,p,q in [('K','x0','x1','next_x0','next_x1'),('G','y0','y1','next_y0','next_y1')]:
  rs.extend([e[p]-co[f+'0']*e[a]-co[f+'2']*e[b],co[f+'0']*e[q]-co[f+'1']*e[p]-e[b]])
 U=sum(r*r for r in rs)
 if not countdown:return U
 load=(e['next_x0']-e['x0'])**2+(e['next_x1']-e['x1'])**2+(e['next_y0']-52891*e['y0']-94920*e['y1'])**2+(e['next_y1']+29036*e['y0']+52109*e['y1'])**2+(e['next_n']-e['n']+1)**2
 return load*(U+e['n']**2+e['next_n']**2)

def degree_line(packet,constants):
 env={p:{} for p in packet['ports']}|{k:pc(v) for k,v in constants.items()}
 env['z']=pv('t')
 if packet['mode']=='computed':env['q_K0']=pv('t')
 if packet['countdown']:env['n']=pv('t')
 out=source_poly(packet,env)[packet['output']];degree=pdegree(out,{'t'})
 expected=(8 if packet['mode']=='computed' else 4)+(2 if packet['countdown'] else 0)
 need(degree==expected,'exact degree line')
 leader=out[('t',)*degree];need(leader==(constants['L']**4 if packet['mode']=='computed' else 1),'degree leader')
 return {'exact_degree':degree,'specialization':'all state and square-root ports zero; z=t; additionally q_K0=t in computed mode, n=t in countdown mode','coefficient_terms':len(out),'polynomial_sha256':phash(out),'leading_coefficient_hex':hex(leader)}


def actual_zero_checks(variants,constants,table,moduli):
 checks=0;wrong=0;loader=0;aliases=0
 for fixture in FOUR_SQUARE_FIXTURES['node_fixtures']:
  i=fixture['index'];row=table[i];h=moduli[i]-1
  need(i in [0,95],'zero selector square fixture')
  for packet in variants.values():
   ports={p:0 for p in packet['ports']};ports['z']=i
   for c in COLS:
    v=row[c[0]][int(c[1])]+constants['T'];roots=fixture['bounds'][c]
    need(all(type(a) is int for a in roots) and len(roots)==4 and sum(a*a for a in roots)==v*(h-v),'large four-square certificate')
    q,r=divmod(constants['C_'+c]-v,moduli[i]);need(r==0,'fixture quotient');ports['q_'+c]=q
    if packet['mode']=='supplied':ports['v_'+c]=v
    ports.update({'bound_'+c+'_'+str(j):a for j,a in enumerate(roots)})
   for f,u,v,a,b in [('K',2,-1,'x','next_x'),('G',-3,4,'y','next_y')]:
    M=row[f];ports[a+'0']=u;ports[a+'1']=v;ports[b+'0']=u*M[0]+v*M[2];ports[b+'1']=u*M[1]+v*M[3]
   need(evaluate(packet,constants,ports)[packet['output']]==0,'full integer tile zero');checks+=1
   ports['next_x1']+=1
   need(evaluate(packet,constants,ports)[packet['output']]>0,'wrong row rejected');wrong+=1
 for packet in variants.values():
  if packet['countdown']:
   for counter in [-2,3]:
    ports={p:(j%7)-3 for j,p in enumerate(packet['ports'])}
    ports.update({'x0':2,'x1':-1,'next_x0':2,'next_x1':-1,'y0':-3,'y1':4,'next_y0':-3*52891+4*94920,'next_y1':3*29036-4*52109,'n':counter,'next_n':counter-1})
    need(evaluate(packet,constants,ports)[packet['output']]==0,'LOAD ignores CRT auxiliary constraints');loader+=1
  # Explicit rational spurious transition: nonzero rows map to zero.
  ports={p:0 for p in packet['ports']};ports['x0']=ports['y0']=1;h=constants['L'];v=constants['T'];roots=FOUR_SQUARE_FIXTURES['rational_alias_bound']
  need(sum(a*a for a in roots)==v*(h-v),'rational alias four squares')
  for c in COLS:
   ports['q_'+c]=Fraction(constants['C_'+c]-v,h+1)
   if packet['mode']=='supplied':ports['v_'+c]=v
   ports.update({'bound_'+c+'_'+str(j):a for j,a in enumerate(roots)})
  need(any(ports['q_'+c].denominator!=1 for c in COLS),'noninteger quotient')
  need(evaluate(packet,constants,ports)[packet['output']]==0,'explicit rational alias');aliases+=1
 return {'full_integer_tile_zeros':checks,'wrong_state_rejections':wrong,'integer_loader_zeros_with_unconstrained_CRT_auxiliaries':loader,'explicit_rational_false_transition_zeros':aliases,'four_square_certificates':FOUR_SQUARE_FIXTURES,'scope':'Two actual selected nodes in both complete modes and both wrappers; complete rational aliases prove real exactness fails. Each saved square decomposition is verified as an exact integer identity; no probable-prime assertion is used.'}

def positive_history(h,local,parent,constants):
 b=Build();signed_names=[];inverse={};positive_ports=[]
 for step in range(h):
  for name in ['next_x0','next_x1','next_y0','next_y1','next_n']+auxiliaries('computed'):
   key='s'+str(step)+'_'+name;pos='positive_'+key;positive_ports.append(pos);signed_names.append(key);inverse[key]=b.sub(pos,'offset')
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
 packet={'duration':h,'domain':'ordinary_x is natural; all listed witness ports are positive integers','witness_ports':['offset']+positive_ports,'ports':['ordinary_x','offset']+positive_ports,'instructions':b.rows,'output':total,'state_reconstruction_rows':40*h,'local_instances':h,'endpoint_rows':7,'final_joins':h,'source_composition':'Copy the full154-row computed countdown at each step after40 shared coordinate subtractions, then the unchanged7-row endpoint and h joins.'}
 packet['ledger'],packet['degree_upper']=audit_packet(packet,CONSTS)
 need(packet['ledger']['total']==195*h+7 and len(packet['witness_ports'])==40*h+1 and packet['degree_upper']<=10,'positive history ledger')
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

def make(root):
 for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'pin '+name)
 parent=read_json(root/'matrix193_unimodular_selector.json');need(parent['source_sha256']==PINS['matrix193_unimodular_selector.py'],'parent self source')
 table=parent['transition_table'];need(type(table) is list and len(table)==96,'table')
 ids=[]
 for row in table:
  need(type(row['tile_id']) is int,'tile id');ids.append(row['tile_id'])
  for f in ['K','G']:
   a=row[f];need(type(a) is list and len(a)==4 and all(type(x) is int for x in a),'matrix')
   need(a[0]*a[3]-a[1]*a[2]==1 and a[0]!=0,'unimodular pivot')
 need(len(set(ids))==96,'distinct tiles')
 values={c:[r[c[0]][int(c[1])] for r in table] for c in COLS}
 L=math.factorial(96);T=max(abs(v) for col in values.values() for v in col)+1;moduli=[1+(i+1)*L for i in range(96)];product=math.prod(moduli)
 need(2*T<min(moduli),'shifted range');need(all(math.gcd(m,n)==1 for i,m in enumerate(moduli) for n in moduli[:i]),'pairwise coprime')
 constants={'L':L,'T':T};quotients={};node_checks=0
 partial=[product//m for m in moduli];inverses=[pow(p,-1,m) for p,m in zip(partial,moduli)]
 for c in COLS:
  C=sum((v+T)*p*inv for v,p,inv in zip(values[c],partial,inverses))%product;constants['C_'+c]=C;quotients[c]=[]
  for m,v in zip(moduli,values[c]):
   residue=v+T;need(0<residue<m and C%m==residue,'CRT match')
   q,r=divmod(C-residue,m);need(r==0,'integer quotient');quotients[c].append(q);node_checks+=1
 fixed={k:{'hex':hex(v),'bit_length':v.bit_length(),'sha256_hex':sha(hex(v).encode())} for k,v in constants.items()}
 variants={};rings={};formal_terms=0;comparisons=0
 for mode in ['supplied','computed']:
  for count in [False,True]:
   name=mode+('_countdown' if count else '_synchronized');packet=emit(mode,count,parent)
   env=source_poly(packet);formula,rs,_=direct_poly(mode,count)
   need(env[packet['output']]==formula,'whole formal polynomial')
   need([env[r] for r in packet['residual_wires']]==rs,'all formal residuals')
   need(pdegree(formula,set(packet['ports']))==packet['degree_upper'],'weighted exact degree')
   packet['formal_identity']={'terms':len(formula),'sha256':phash(formula),'residual_terms':[len(r) for r in rs],'constants_are_independent_formal_ports':True};formal_terms+=len(formula)
   packet['degree_certificate']=degree_line(packet,constants)
   # Bounded signed and rational complete-source checks against direct formulas.
   for seed in range(12):
    ports={p:((seed+3)*(i+7)%23)-11 for i,p in enumerate(packet['ports'])}
    if seed>=8:ports={p:Fraction(v,((i+seed)%3)+1) for i,(p,v) in enumerate(ports.items())}
    result=evaluate(packet,constants,ports)[packet['output']]
    need(result==direct_numeric(mode,count,constants,ports),'full signed/rational reference');comparisons+=1
   variants[name]=packet;rings[name]=formula
 # The full computed polynomial is the exact supplied-v pullback.
 pullbacks=[]
 for count in [False,True]:
  suffix='_countdown' if count else '_synchronized';computed=variants['computed'+suffix];supplied=variants['supplied'+suffix]
  _,_,rem=direct_poly('computed',count);mapped=source_poly(supplied,{'v_'+c:rem[c] for c in COLS})
  need(mapped[supplied['output']]==rings['computed'+suffix],'whole remainder pullback')
  need(all(mapped[r]=={} for r in supplied['quotient_residual_wires']),'quotient residual vanishes')
  pullbacks.append({'countdown':count,'coefficient_terms':len(rings['computed'+suffix]),'sha256':phash(rings['computed'+suffix])})
 # Full matched coefficient/node identities, independent of four-square construction.
 node_actions=0
 for i,row in enumerate(table):
  got={c:constants['C_'+c]-moduli[i]*quotients[c][i]-T for c in COLS}
  for family in ['K','G']:
   a,b,c,d=row[family]
   for u,v in [(0,0),(1,0),(-2,3),(Fraction(2,3),Fraction(-5,7))]:
    p=a*u+c*v;q=b*u+d*v
    need(p-got[family+'0']*u-got[family+'2']*v==0,'row0')
    need(got[family+'0']*q-got[family+'1']*p-v==0,'row1');node_actions+=1
 zeros=actual_zero_checks(variants,constants,table,moduli)
 positive={str(h):positive_history(h,variants['computed_countdown'],parent,constants) for h in [1,2]}
 endpoint=parent['endpoint'];need(endpoint['ledger']=={'M':3,'A':4,'operations':7} if 'operations' in endpoint['ledger'] else endpoint['ledger']=={'M':3,'A':4,'total':7},'endpoint ledger')
 return {'schema':'matrix193-crt-selector-v1','status':'PASS_COMPLETE_INTEGER_LOCAL_RELATIONS','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'predecessor_code_executed':False,'transition_table':table,'selector_to_tile_id':ids,'fixed_numeral_recipe':{'L':'96!','T':'1+maximum absolute value of the six retained actual columns','moduli':moduli,'common_product_bits':product.bit_length(),'CRT':'For each column c: C_c=sum_i (entry_i+T)*(M/m_i)*inverse(M/m_i mod m_i), reduced modulo M=product_i m_i. All operations are fixed-data compilation.','fixed_numerals':fixed,'node_coefficient_checks':node_checks,'pairwise_gcd_checks':96*95//2,'maximum_fixed_numeral_bits':max(v.bit_length() for v in constants.values())},'variants':variants,'full_polynomial_pullbacks':pullbacks,'finite_checks':{'complete_signed_rational_source_comparisons':comparisons,'including_rational':16,'exact_row_actions':node_actions,'formal_coefficient_entries':formal_terms,'full_integer_and_domain_checks':zeros},'positive_fixed_duration_sources':positive,'uniform_context_extension':{'scope':'Any inherited fixed contexts, with all paired actions in Hprime subset Gamma1(5); pivots are1 mod5 and cannot vanish. Fixed numeric arrays here remain the selected fixture.','L_recipe':'96! * ceil((2T+1)/96!), where T=1+max absolute retained entry; choose at least one multiple.','countdown_operations':154,'signed_auxiliary_witnesses':35},'initial_state':parent['initial_state'],'endpoint':endpoint,'fixed_duration_bounds':{'computed_countdown':{'operations':'155h+7','signed_witnesses':'40h','degree_upper':10},'supplied_countdown':{'operations':'173h+7','signed_witnesses':'46h','degree_upper':6},'computed_synchronized':{'operations':'129h+5','signed_witnesses':'39h','degree_upper':8},'positive_computed_countdown':{'operations':'195h+7','positive_witnesses':'40h+1','degree_upper':10}},'scope':'Exact signed-integer local and fixed-duration predicates. SOS is globally real nonnegative, but real transition exactness is false. Unbounded duration packing remains unpaid. The fixed-duration positive-coordinate conversion is paid explicitly.'}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--expect',type=Path);g.add_argument('--output',type=Path);a=p.parse_args();r=make(a.root)
 if a.output:
  with a.output.open('x') as f:json.dump(r,f,indent=2,sort_keys=True);f.write('\n')
 else:need(exact(r,read_json(a.expect)),'exact receipt')
 print('PASS: complete integer CRT selectors 128/154 and146/172; full arrays, source identities and fixed data')

if __name__=='__main__':main()
