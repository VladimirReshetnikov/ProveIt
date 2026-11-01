import json,re,random
from pathlib import Path
D=Path(__file__).resolve().parent;R=D.parents[3];P=R/'Computability/DiophantineConsistency/research/adaptive-square-sums49';c=json.loads((P/'candidate.json').read_text());s=(P/'equation4-49-display.tex').read_text();body=re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}',s[s.index('All other symbols'):],re.S).group(1).strip()[:-1];body=body.replace(r'\quad','').replace('\\\\',',');defs=[x.strip() for x in body.split(',') if x.strip()]
variables=['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma','vartheta','psi','varphi','epsilon','c','a','ell','h','t','s','x','m','n','p','j','d','o','e','z','delta','kappa','lambda','sigma','tau','chi','theta','nu','Q','N','O','P','S','A','i','w','y']
expected=['qm','q','C','U','productVariable2','k','namedBt','rankSeedVariable','root_skew','H','deltaVariable','offsetVariable','M','R','Z','Dstar','V','scaledIndexVariable','A0','A1','auxResidual','g72','squareDifference','scaleDifference','mainScaleDifference','rankDifference','cDifference','aDifference','ellDifference','wDifference','cubeDifference','productDifference','fSquareDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference','qSquareDifference','product2Difference','psiSquareDifference','ellProductDifference','varphiSquareDifference','scaledIndexDifference','ySquareDifference','qSignedDifference','deltaProductDifference','rankSeedDifference','ySumDifference','rootSkewDifference','offsetDifference','gammaProductDifference','timeProductDifference']
assert len(variables)==49 and len(defs)==len(expected)==53
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
for trial in range(25):
 rng=random.Random(80231+trial);vals={x:rng.randint(1,3) for x in variables};vals.update({x:rng.randint(1,3) for x in ('beta','K','mu','omega')})
 dag={name:vals[var] for name,var in zip(c['witnesses'],variables)};dag.update({name:vals[var] for name,var in zip(c['fixed_numerals'],('beta','K','mu','omega'))})
 for name,op,a,b in c['source']:
  aa=dag[a] if isinstance(a,str) else a;bb=dag[b] if isinstance(b,str) else b
  dag[name]={'+':lambda:aa+bb,'-':lambda:aa-bb,'*':lambda:aa*bb}[op]()
 for text,want in zip(defs,expected):
  lhs,rhs=text.split('=',1);lhs=tokens(lhs.strip());assert len(lhs)==1
  value=expression(rhs,vals);assert value==dag[want],(trial,lhs,want,value,dag[want]);vals[lhs[0]]=value
print('PASS independent evaluation of 54 definitions (35 residuals), 25 deterministic assignments, each of 185 candidate gates')
