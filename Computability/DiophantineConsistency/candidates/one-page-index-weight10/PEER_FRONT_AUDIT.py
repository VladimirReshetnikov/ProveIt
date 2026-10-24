#!/usr/bin/env python3
"""Independent parse of the actual TeX arithmetic front, without renderer imports."""
import argparse
from collections import Counter
from hashlib import sha256
from pathlib import Path
import gzip,json,re,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',required=True,type=Path)
args=parser.parse_args()
PAGE=ROOT/'candidates/one-page-index-weight10';OLD=ROOT/'candidates/one-page-short10';FRONT=ROOT/'research/ten-positive-index-weight'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def digest(b):return sha256(b).hexdigest()
packet=json.loads((FRONT/'zero98.json').read_bytes())
tex=(PAGE/'equation-template.tex').read_text();oldtex=(OLD/'equation-template.tex').read_text()
marker=r'\textbf{The four fixed integers.}'
need(tex.count(marker)==oldtex.count(marker)==1,'one constant body marker')
body=tex.split(marker,1)[1];oldbody=oldtex.split(marker,1)[1]
need(body==oldbody,'complete verbatim constant body including footer')
seed=(OLD/'SEED.txt').read_text().strip();alphabet='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
need(len(seed)==436 and set(seed)<=set(alphabet),'all436 base62 seed characters')
need(tex.count('%%SEED%%')==1 and alphabet in body,'single seed slot and ordered62 alphabet')
need((PAGE/'SEED.txt').read_bytes()==(OLD/'SEED.txt').read_bytes(),'complete generated page seed bytes unchanged')
unknowns=['J','F','alpha','i','T','w','Y','n','eta','zeta']
need(packet['witnesses']==unknowns and packet['fixed_numerals']==['beta','K0','MC','MF'],'exact ten unknowns and four free coefficients')
need(r'J,F,\alpha,i,T,w,Y,n,\eta,\zeta\in\mathbb Z_{>0}' in tex,'printed strictly positive input order')
# Nodes are interned by exact syntax modulo AC and integer arithmetic only.
# Both actual literal gates and actual parsed TeX use this independent algebra.
nodes=[];interned={}
def make(v):
 if v not in interned:interned[v]=len(nodes);nodes.append(v)
 return interned[v]
def atom(v):return make(('i',v)) if type(v) is int else make(('v',v))
def operation(op,a,b):
 if op=='-':return make(('minus',a,b))
 items=[];constant=0 if op=='+' else 1
 for p in [a,b]:
  expanded=nodes[p][1:] if nodes[p][0]==op else [p]
  for q in expanded:
   if nodes[q][0]=='i':constant=constant+nodes[q][1] if op=='+' else constant*nodes[q][1]
   else:items.append(q)
 if op=='*' and constant==0:return atom(0)
 if constant!=(0 if op=='+' else 1) or not items:items.append(atom(constant))
 return items[0] if len(items)==1 else make((op,*sorted(items)))
def power(a,n):
 need(type(n) is int and n>=0,'fixed nonnegative integer exponent')
 p=atom(1)
 for _ in range(n):p=operation('*',p,a)
 return p
actual={n:atom(n) for n in unknowns+packet['fixed_numerals']}
for name,op,a,b in packet['source']:
 need(name not in actual,'fresh literal register')
 actual[name]=operation(op,atom(a) if type(a) is int else actual[a],atom(b) if type(b) is int else actual[b])
deps={row[0]:[x for x in row[2:] if type(x) is not int] for row in packet['source']}
live=set();todo=[packet['output']]
while todo:
 x=todo.pop()
 if x in live:continue
 live.add(x);todo.extend(deps.get(x,[]))
need(live==set(actual),'every literal gate,input and fixed port is live')
# Complete visual-to-literal aliases, including all thirteen tail registers.
alias={r'q_-':'bJ',r'\alpha':'alpha',r'\eta':'eta',r'\zeta':'zeta',r'\beta':'beta',
 r'\mu':'mu',r'\Delta':'Dp',r'\delta':'delta',r'V_0':'V0',r'\ell':'V0k',r'D_\tau':'Dtau',
 r'B_t':'Bt',r'D_f':'Df',r'D_y':'Dnum',r'K_2':'Kpos',r'P_1':'P1',r'A_\tau':'fa',r'A_f':'fb',r'A_y':'fc',
 r'\Sigma_1':'U',r'\Sigma_2':'ab',r'V_N':'aXb',r'T\prime':'Tp',"T'":'Tp',"b'":'cTR',r'M_C':'MC',r'M_F':'MF',
 'A':'Am1','H':'Hp','K':'K0','M':'Mtot','Z':'Znum','S':'fs','P':'Po','U':'sc','E':'Pe'}
for n in unknowns+['q','C','X','k','c','I','R','e','Q','V','L']:alias.setdefault(n,n)
ordered=sorted(alias,key=len,reverse=True)
def tokenize(s):
 out=[];j=0
 while j<len(s):
  if s[j].isspace():j+=1;continue
  if s[j] in '+-*^()[]{}':out.append(s[j]);j+=1;continue
  if s[j].isdigit():
   m=re.match(r'\d+',s[j:]);out.append(int(m[0]));j+=len(m[0]);continue
  key=next((k for k in ordered if s.startswith(k,j)),None)
  need(key is not None,'unparsed TeX token '+s[j:]);out.append(('v',alias[key]));j+=len(key)
 return out
printed={n:atom(n) for n in unknowns+packet['fixed_numerals']}
def parse(s):
 toks=tokenize(s);pos=0
 def expression():
  nonlocal pos
  a=product()
  while pos<len(toks) and toks[pos] in ['+','-']:
   op=toks[pos];pos+=1;a=operation(op,a,product())
  return a
 def product():
  nonlocal pos
  a=powered()
  while pos<len(toks):
   t=toks[pos]
   if t=='*':pos+=1;a=operation('*',a,powered())
   elif type(t) is int or isinstance(t,tuple) or t in ['(','[','{']:a=operation('*',a,powered())
   else:break
  return a
 def powered():
  nonlocal pos
  a=primary()
  if pos<len(toks) and toks[pos]=='^':
   pos+=1;n=toks[pos];pos+=1
   if n=='{':n=toks[pos];pos+=1;need(toks[pos]=='}','fixed exponent closing brace');pos+=1
   a=power(a,n)
  return a
 def primary():
  nonlocal pos
  need(pos<len(toks),'complete expression operand');t=toks[pos];pos+=1
  if type(t) is int:return atom(t)
  if isinstance(t,tuple):need(t[1] in printed,'prior printed abbreviation '+t[1]);return printed[t[1]]
  need(t in ['(','[','{'],'valid group opening');a=expression();need(toks[pos]=={'(':')','[':']','{':'}'}[t],'matching group');pos+=1;return a
 result=expression();need(pos==len(toks),'entire TeX expression consumed');return result
front=tex.split('All other symbols in the equation are polynomial abbreviations:',1)[1].split(marker,1)[0]
math=front.split(r'\begin{gathered}',1)[1].split(r'\end{gathered}',1)[0]
for command in [r'\qquad',r'\quad',r'\\']:math=math.replace(command,' ')
assignments=[]
for statement in math.split(','):
 if not statement.strip():continue
 need(statement.count('=')==1,'single displayed assignment')
 lhs,rhs=statement.split('=');rhs=rhs.strip().removesuffix('.');tokens=tokenize(lhs.strip());need(len(tokens)==1 and isinstance(tokens[0],tuple),'single lhs alias')
 name=tokens[0][1];need(name in actual and name not in printed,'unique actual lhs '+name)
 value=parse(rhs);need(value==actual[name],'actual TeX definition equals literal register '+name)
 printed[name]=value;assignments.append(dict(tex_lhs=lhs.strip(),literal_register=name))
box=front.split(r'\boxed{',1)[1].split('}',1)[0]
lhs,rhs=box.split('=');need(rhs=='0.','single equation zero plus punctuation')
need(parse(lhs)==actual[packet['output']],'entire actual printed equation equals literal98-gate output')
counts=Counter(r[1] for r in packet['source']);need(len(packet['source'])==packet['operations']==98 and counts==Counter({'*':58,'+':22,'-':18}),'complete actual operation count')
# Mutations of real TeX front expressions must change their actual literal register.
controls=[]
for name,bad in [('L','HI+b\''),('Am1',r'\mu Y(X+1)+1'),('Dp','A(A+1)'),('Znum',r'P_1\mu^2[H(n+V+LB_t)+K_2]+H[\mu^2(q_-Y-q^3B_t)-P_1e]')]:
 need(parse(bad)!=actual[name],'reject changed '+name);controls.append(name)
# Each coefficient payload transfer is whole and the shifted MF is copied once.
portfiles={'beta':'beta.bin.gz','K0':'K.bin.gz','MC':'MC.bin.gz','MF':'MF_source.bin.gz'};ports={};values={}
for n,f in portfiles.items():
 blob=(OLD/'coefficients'/f).read_bytes();need((PAGE/'coefficients'/f).read_bytes()==blob,'complete copied BFS payload '+n);raw=gzip.decompress(blob);values[n]=int.from_bytes(raw,'little')
 ports[n]=dict(file=f,gzip_sha256=digest(blob),raw_sha256=digest(raw),bits=values[n].bit_length())
beta=values['beta'];need(beta>=31 and beta%2==1 and values['K0']>0 and 0<values['MC']<beta<values['MF']<2*beta,'whole coherent BFS tuple satisfies uniform box')
need((PAGE/'parent-polynomial.json').read_bytes()==(FRONT/'zero98.json').read_bytes(),'complete generated parent bytes')
generated=json.loads((PAGE/'polynomial.json').read_bytes())
expected=dict(packet);expected.update(name='one_page_index_weight10_bfs44_degree360',proof='../../research/ten-positive-index-weight/PROOF.md',parent_sha256=digest((FRONT/'zero98.json').read_bytes()),coefficient_binding=dict(path='coefficients/',tuple='whole BFS-renamed compact44, corrected initializer; MF_source shifted exactly once',ports=ports))
need(generated==expected,'entire generated page graph, source/witnesses/output and coherent four-port binding')
renderer=(ROOT/'tools/render_index_weight10_page.py').read_text()
needed_glyphs=['α','η','ζ','β','ρ','µ','κ','ϱ','∆','Σ','δ','τ','Φ','ν','σ','ℓ']
missing_glyphs=[g for g in needed_glyphs if repr(g) not in renderer]
need(not missing_glyphs,'renderer declares every required Greek and ell glyph')
report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),audit_self_sha256=digest(Path(__file__).read_bytes()),generated_page_whole_graph_and_ports_authenticated=True,scope='Independent actual-TeX front parse, full98 literal graph binding, aliases, verbatim constant body and coherent payload transfer only. No PDF rendering, tuple reconstruction, ordinary proof review or promotion.',
 parsed_aliases=assignments,all_parsed_definitions_match=True,complete_output_matches=True,all98_gates_live=True,operations=98,operation_breakdown=dict(counts),declared_exact_degree=packet['exact_degree'],
 constant_body_sha256=digest(body.encode()),constant_body_verbatim=True,complete_seed_characters=len(seed),seed_sha256=digest((OLD/'SEED.txt').read_bytes()),ordered_alphabet=alphabet,ports=ports,
 renderer_glyph_check_missing=missing_glyphs,rejected_real_formula_mutations=controls,
 sha256={str(p.relative_to(ROOT)):digest(p.read_bytes()) for p in [ROOT/'tools/render_index_weight10_page.py',PAGE/'equation-template.tex',PAGE/'README.md',FRONT/'zero98.json',OLD/'equation-template.tex',PAGE/'polynomial.json',PAGE/'parent-polynomial.json',PAGE/'SEED.txt']})
data=(json.dumps(report,indent=2,sort_keys=True)+'\n').encode()
if args.output.exists():need(args.output.read_bytes()==data,'refuse different existing audit output')
else:args.output.write_bytes(data)
print(json.dumps({k:report[k] for k in ['status','operations','operation_breakdown','declared_exact_degree','constant_body_verbatim','complete_seed_characters','renderer_glyph_check_missing']},sort_keys=True));print('parsed definitions',len(assignments))
