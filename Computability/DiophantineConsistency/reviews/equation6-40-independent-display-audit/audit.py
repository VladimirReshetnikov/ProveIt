import json,re,random,hashlib
from pathlib import Path
D=Path(__file__).resolve().parent;R=D.parents[3];P=R/'Computability/DiophantineConsistency';C=P/'research/adaptive-square-sums40';c=json.loads((C/'candidate.json').read_text());s=(C/'equation6-40-display.tex').read_text();body=re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}',s[s.index('All other symbols'):],re.S).group(1).strip()[:-1];body=body.replace(r'\quad','').replace('\\\\',',');defs=[x.strip() for x in body.split(',') if x.strip()]
variables=['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma','vartheta','psi','varphi','epsilon','c','ell','h','t','s','x','m','n','p','j','d','o','e','z','delta','kappa','lambda','sigma','tau','chi','theta','nu','Q']
expected=['qm','q','C','U','a','productVariable2','k','namedBt','H','deltaVariable','b0','M','R','Z','Dstar','V','scaledIndexVariable','A0','A1','auxResidual','g72','squareDifference','scaleDifference','mainScaleDifference','rankDifference','cDifference','ellDifference','wDifference','cubeDifference','productDifference','fSquareDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference','qSquareDifference','product2Difference','psiSquareDifference','ellProductDifference','varphiSquareDifference','scaledIndexDifference','ySquareDifference','qSignedDifference']
assert len(variables)==40 and len(defs)==len(expected)==44
# New evaluator: independent tokenizer and Python expression translation; no imports from repo checker.
def identifier(t):
 if t.startswith('\\mathcal{'):return 'cal'+t[9:-1]
 if t.startswith('\\mathfrak{'):return 'frak'+t[10:-1]
 return t[1:] if t.startswith('\\') else t
def tokens(s):
 pat=r'\\mathcal\{[A-Z]\}|\\mathfrak\{[A-Z]\}|\\[a-zA-Z]+|[A-Za-z]|\d+|[()+\-*\[\]^]'
 out=re.findall(pat,s); leftover=re.sub(pat,'',s)
 assert not leftover.strip(),(s,leftover)
 return [identifier(x) for x in out]
def expression(expr,env):
 ts=tokens(expr);out=[];prev=False
 for t in ts:
  atom=t[0].isalnum() or t in '(['
  if prev and atom:out.append('*')
  if t=='^':out.append('**');prev=False
  elif t=='[':out.append('(');prev=False
  elif t==']':out.append(')');prev=True
  elif t=='(':out.append('(');prev=False
  elif t==')':out.append(')');prev=True
  elif t in ('+','-','*'):out.append(t);prev=False
  else:out.append(t if t.isdigit() else 'v_'+t);prev=True
 return eval(''.join(out),{'__builtins__':{}},{'v_'+k:v for k,v in env.items()})
class Polynomial:
 def __init__(self,terms):self.terms={e:c for e,c in terms.items() if c}
 @staticmethod
 def lift(x):return x if isinstance(x,Polynomial) else Polynomial({(0,)*44:x})
 def __add__(self,x):
  d=self.terms.copy()
  for e,c in self.lift(x).terms.items():d[e]=d.get(e,0)+c
  return Polynomial(d)
 __radd__=__add__
 def __neg__(self):return Polynomial({e:-c for e,c in self.terms.items()})
 def __sub__(self,x):return self+-self.lift(x)
 def __rsub__(self,x):return self.lift(x)+-self
 def __mul__(self,x):
  d={}
  for a,coefficient in self.terms.items():
   for b,other in self.lift(x).terms.items():
    e=tuple(i+j for i,j in zip(a,b));d[e]=d.get(e,0)+coefficient*other
  return Polynomial(d)
 __rmul__=__mul__
 def __pow__(self,n):
  assert type(n)==int and n>=0
  a=self.lift(1)
  for _ in range(n):a=a*self
  return a
 def __eq__(self,x):return self.terms==self.lift(x).terms

all_symbols=variables+['beta','K','mu','omega'];assert len(all_symbols)==len(set(all_symbols))==44
vals={}
for i,name in enumerate(all_symbols):
 e=[0]*44;e[i]=1;vals[name]=Polynomial({tuple(e):1})
dag={name:vals[var] for name,var in zip(c['witnesses'],variables)};dag.update({name:vals[var] for name,var in zip(c['fixed_numerals'],('beta','K','mu','omega'))})
for name,op,a,b in c['source']:
 aa=dag[a] if isinstance(a,str) else Polynomial.lift(a);bb=dag[b] if isinstance(b,str) else Polynomial.lift(b)
 dag[name]={'+':lambda:aa+bb,'-':lambda:aa-bb,'*':lambda:aa*bb}[op]()
for text,want in zip(defs,expected):
 lhs,rhs=text.split('=',1);lhs=tokens(lhs.strip());assert len(lhs)==1
 value=expression(rhs,vals);assert value==dag[want],(lhs,want);vals[lhs[0]]=value
unknown=re.search(r'\\begin\{gathered\}(.*?)\\in\\mathbb Z_\{>0\}',s,re.S)
assert unknown
printed=[identifier(x.strip()) for x in unknown.group(1).replace('\\\\','').split(',')]
assert printed==variables and len(set(printed))==40
assert hashlib.sha256((C/'candidate.json').read_bytes()).hexdigest()=='d02609f153f86f4ef73ca077f0aaef171ca779ead3013131fa13aa187656de37'
tex=(P/'equation6-40.tex').read_text();assert s in tex
labels=[definition.split('=',1)[0].strip() for definition in defs[17:]]
expected_sum=r'\begin{split}'+'+'.join(x+'^2' for x in labels)+r'=0.\end{split}'
assert len(labels)==len(set(labels))==27
def check_sum(text):
 match=re.search(r'The single Diophantine equation is\s*\\\[(.*?)\\\]',text,re.S)
 if not match:return False
 return re.sub(r'\s+','',match.group(1)).replace('&','').replace('\\\\','')==expected_sum
assert check_sum(s)
mutations=[s.replace(r'\mathcal{P}^2','resA^2',1),s.replace(r'\begin{split}',r'1+\begin{split}',1)]
assert all(t!=s and not check_sum(t) for t in mutations)
source=(P/'Lean/DiophantineConsistency/AdaptiveAQ40Literal.lean').read_text();block=source.split('def literal (p : Fin 4 → ℤ) : Expr (Fin 40) :=\n',1)[1].split('\ntheorem new_literal ',1)[0]
varrows=re.findall(r'^  let (\w+) : Expr \(Fin 40\) := \.var (\d+)$',block,re.M)
portrows=re.findall(r'^  let (\w+) : Expr \(Fin 40\) := \.constant \(p (\d+)\)$',block,re.M)
gaterows=re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',block,re.M)
assert varrows==[(v,str(i)) for i,v in enumerate(c['witnesses'])]
assert portrows==[(v,str(i)) for i,v in enumerate(c['fixed_numerals'])]
norm=lambda x:int(x) if x.isdigit() else x
assert [[n,op,norm(a),norm(b)] for n,a,op,b in gaterows]==c['source'] and block.strip().splitlines()[-1].strip()==c['output']
# Independently compare the numbered evaluator lines with the pinned DAG.
circuit_inputs=['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma','vartheta','psi','varphi','epsilon','cNamed','ellNamed','h','t','s','x','m','n','p','j','d','o','e','z','delta','kappa','lambda','sigma','tau','chi','theta','nu','Q']
alias=dict(zip(c['witnesses'],circuit_inputs));alias.update(dict(zip(c['fixed_numerals'],['beta','K','mu','omega'])))
alias.update({'qm':'b','Bt':'W','b0':'L','Dstar':'D','G':'rankseed','namedBt':'WNamed',
 'rankDifference':'rankDiff','rankConstraint':'rankCheck','finalWithRank':'result17',
 'mainScaleDifference':'mainDiff','mainScaleConstraint':'mainCheck','finalWithMainScale':'result16',
 'scaleDifference':'scaleDiff','scaleConstraint':'scaleCheck','finalWithScale':'final',
 'squareConstraint':'constraint','squareDifference':'difference','sumWithConstraint':'result'})
def fmt(x):return alias.get(str(x),str(x)).replace('_',r'\_')
lines=[line for line in tex.splitlines() if line[:1].isdigit() and '. ' in line and ' = ' in line and line.endswith(r'\\')]
assert len(set(alias[n] for n in c['witnesses']+c['fixed_numerals']))==44
assert len(lines)==len(c['source'])==160
for i,(line,(name,op,a,b)) in enumerate(zip(lines,c['source']),1):
 assert line==f'{i}. {fmt(name)} = {fmt(a)} {op} {fmt(b)}'+r'\\',(i,line)
assert r'\mathcal{A}' not in labels and r'\mathcal A' in tex
print(json.dumps({'status':'PASS_INDEPENDENT_EXACT_DISPLAY40_AUDIT','candidate_sha256':hashlib.sha256((C/'candidate.json').read_bytes()).hexdigest(),'tex_sha256':hashlib.sha256(tex.encode()).hexdigest(),'display_sha256':hashlib.sha256(s.encode()).hexdigest(),'lean_sha256':hashlib.sha256(source.encode()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'unknowns':len(variables),'fixed_ports':4,'source_gates':len(gaterows),'display_circuit_rows':len(lines),'raw_sum_negative_controls':len(mutations),'definitions':len(defs),'residuals':len(labels),'scope':'Exact independent sparse-polynomial equality for displayed definitions and sum wiring; exact Lean literal/candidate gate match. Separate provenance and interpretation bridges are not re-proved.'},indent=2,sort_keys=True))
