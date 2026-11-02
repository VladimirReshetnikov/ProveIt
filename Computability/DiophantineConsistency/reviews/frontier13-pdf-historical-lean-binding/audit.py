#!/usr/bin/env python3
"""Independent finite binding of both 13-variable historical equations."""
import gzip,hashlib,json,re,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
sys.set_int_max_str_digits(0)
D=Path(__file__).resolve().parent;ROOT=D.parents[1];REV=ROOT/'reviews';RESEARCH=ROOT/'research'
SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2');PARENT=Path('/tmp/ipra-aq29-fresh-project-pair')
PORT=REV/'equation14-historical-literal-binding';PR=REV/'equation14-historical-literal-binding-independent'
COEFF=ROOT/'candidates/one-page-padding-staircase-carrier65-2011';FRONT=RESEARCH/'ipra-standard-13-frontier/draft-src'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());raw=lambda b:hashlib.sha256(b).hexdigest()
cases=[{'label':'sum87','graph':RESEARCH/'adaptive-square-sums/candidate.json','tex':ROOT/'equation36.tex','pdf':ROOT/'equation36.pdf',
        'literal':FRONT/'AdaptiveDirectOrdinateSquareSumsLiteral.lean','start':'def literal','end':'\n\n/-- The generated DAG',
        'pin':'11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828','n':87},
       {'label':'product86','graph':RESEARCH/'adaptive-direct-ordinate86/candidate.json','tex':ROOT/'equation86.tex','pdf':ROOT/'equation86.pdf',
        'literal':SNAP/'src/DiophantineConsistency/AdaptiveDirectOrdinate86Literal.lean','start':'def expressionAt86','end':'\ndef contextAt',
        'pin':'e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f','n':86}]
files=[Path(__file__).resolve(),ROOT/'equation.tex',SNAP/'manifest.json',PARENT/'author/state.json',PARENT/'peer/state.json',
       REV/'fresh-project-pair-independent-audit/receipt.json',REV/'fresh-project-pair-independent-audit/terminal-observation.json',
       PORT/'ports-receipt.json',PORT/'printed-constants-repeat.json',PR/'receipt.json',PR/'terminal-observation.json',COEFF/'polynomial.json',
       FRONT/'IPRASquareSumsNative.lean',FRONT/'IPRAStandardSquareSums13.lean',FRONT/'IPRAStandardProduct13.lean']
for c in cases:files.extend(c[x] for x in ('graph','tex','pdf','literal'))
carrier=J(COEFF/'polynomial.json');files += [PORT/'port-outputs'/f'port{i}.txt.gz' for i in range(4)]
files += [COEFF/'coefficients'/carrier['coefficient_binding']['ports'][n]['file'] for n in carrier['fixed_numerals']]
before={str(p.resolve()):H(p) for p in files}
assert 'AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports' in (FRONT/'IPRAStandardSquareSums13.lean').read_text()
assert 'IPRASquareSumsNative.literal_equivalence' in (FRONT/'IPRAStandardSquareSums13.lean').read_text()
assert 'AdaptiveDirectOrdinate86Literal.naturalExpression86' in (FRONT/'IPRAStandardProduct13.lean').read_text()
assert 'HAAdaptiveDirectOrdinate86.polynomialBridge' in (FRONT/'IPRAStandardProduct13.lean').read_text()
names_expected=['J','F','alpha','f','i','T','X','Y','r','eta','zeta','y','gamma']
ports_expected=['beta','K0','MC','MF']

# Sparse integer polynomials; no general TeX or PDF semantics are assumed.
z=(0,)*17
def lift(n):return {} if n==0 else {z:n}
def add(a,b,sign=1):
 d=a.copy()
 for k,v in b.items():d[k]=d.get(k,0)+sign*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d={}
 for ka,va in a.items():
  for kb,vb in b.items():
   k=tuple(x+y for x,y in zip(ka,kb));d[k]=d.get(k,0)+va*vb
 return {k:v for k,v in d.items() if v}
token=re.compile(r'\\[A-Za-z]+|@[PDQR]|[A-Za-z]|[0-9]+|[+\-^=()\[\]]')
def expression(tokens,env,pos):
 def peek():return tokens[pos[0]] if pos[0]<len(tokens) else None
 def atom():
  t=peek();assert t is not None;pos[0]+=1
  if t in ('(', '['):
   v=expr();assert peek()==(')' if t=='(' else ']');pos[0]+=1
  elif t.isdecimal():v=lift(int(t))
  else:assert t in env,(t,tokens);v=env[t]
  if peek()=='^':
   pos[0]+=1;n=peek();assert n is not None and n.isdecimal() and int(n)<=3;pos[0]+=1;base=v;v=lift(1)
   for _ in range(int(n)):v=mul(v,base)
  return v
 def product():
  v=atom()
  while peek() is not None and peek() not in ('+','-',')',']','='):v=mul(v,atom())
  return v
 def expr():
  v=product()
  while peek() in ('+','-'):
   op=peek();pos[0]+=1;v=add(v,product(),1 if op=='+' else -1)
  return v
 return expr()
def tokens_of(s):
 tokens=token.findall(s);assert ''.join(tokens)==re.sub(r'\s+','',s)
 return [x[1:] if x.startswith('\\') else x for x in tokens]
symbol={'J':'J','F':'F','alpha':'alpha','f':'f','g':'i','T':'T','X':'X','Y':'Y','xi':'r','eta':'eta',
        'zeta':'zeta','upsilon':'y','gamma':'gamma','beta':'beta','K':'K0','mu':'MC','omega':'MF'}
defs={'b':'qm','q':'q','C':'C','U':'U','E':'E','k':'k','ell':'ell','c':'c','a':'a','H':'H','Delta':'Delta',
      'L':'b0','M':'M','W':'Bt','R':'R','Z':'Z','D':'Dstar','I':'I','Q':'Q','V':'V'}
rename={'r':'xi','i':'g','y':'upsilon','K0':'K','MC':'mu','MF':'omega','qm':'b','Bt':'W','b0':'L','Dstar':'D','G':'rankseed'}
fmt=lambda x:rename.get(str(x),str(x)).replace('_',r'\_')
original=ROOT/'equation.tex';begin=r'\textbf{The four fixed integers.}';end=r'\endgroup'
def block(t):
 i=t.index(begin);return t[i:t.index(end,t.index(r'\textbf{The integer $\mathcal A$',i))+len(end)]
assert raw(block(original.read_text()).encode())=='e5e7b58b54e57badc97ba6ee7f7577ec8e858c88189474723ce28ae629b0a6c6'
builds={};definition_counts={}
for case in cases:
 assert H(case['graph'])==case['pin'];c=J(case['graph']);assert c['witnesses']==names_expected and c['fixed_numerals']==ports_expected and len(c['source'])==case['n']
 signature=case['start']+' (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n'
 def check_literal(text):
  assert text.count(signature)==1;body=text.split(signature,1)[1].split(case['end'],1)[0].rstrip('\n').splitlines()
  want=[f'  let {n} : Expr (Fin 13) := .var {i}' for i,n in enumerate(names_expected)]
  want += [f'  let {n} : Expr (Fin 13) := .constant (p {i})' for i,n in enumerate(ports_expected)]
  want += [f'  let {n} := {a} {op} {b}' for n,op,a,b in c['source']];want += ['  '+c['output']]
  assert body==want
 source=case['literal'].read_text();check_literal(source);pre,body=source.split(signature,1)
 for old,new in [('.var 0','.var 1'),('.constant (p 0)','.constant (p 1)'),('let qm := J * beta','let qm := J + beta')]:
  changed=body.replace(old,new,1);assert changed!=body
  try:check_literal(pre+signature+changed)
  except AssertionError:pass
  else:raise AssertionError('literal mutation accepted')
 g={}
 for i,n in enumerate(names_expected+ports_expected):
  k=list(z);k[i]=1;g[n]={tuple(k):1}
 skip={'firstSquare','mainSquare','auxSquare','strongSquare','firstMain','firstMainAux','sumSquares','g86','g87','g88','P13'}
 for n,op,a,b in c['source']:
  if n in skip:continue
  x=lift(a) if isinstance(a,int) else g[a];y=lift(b) if isinstance(b,int) else g[b]
  g[n]=add(x,y) if op=='+' else add(x,y,-1) if op=='-' else mul(x,y)
 text=case['tex'].read_text();display=text.split('% BEGIN VERIFIED DISPLAY\n',1)[1].split('% END VERIFIED DISPLAY',1)[0]
 u=re.search(r'variables\s*\\\[(.*?)\\in\\mathbb Z_\{>0\}\.\s*\\\]',display,re.S);assert u
 assert [x.strip().lstrip('\\') for x in u[1].split(',')]==['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma']
 body=re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}',display,re.S)[1].replace('\\\\',',').replace(r'\quad','').strip();assert body.endswith('.')
 for ch in 'PDQR':body=body.replace('\\mathcal{'+ch+'}','@'+ch)
 exp=dict(defs)
 if case['label']=='sum87':exp.update({'@P':'A0','@D':'A1','@Q':'auxResidual','@R':'g72'})
 env={k:g[v] for k,v in symbol.items()};seen=[]
 for definition in (x for x in body[:-1].split(',') if x.strip()):
  tokens=tokens_of(definition);lhs=tokens[0];assert lhs in exp and lhs not in seen and tokens[1]=='='
  pos=[2];value=expression(tokens,env,pos);assert pos[0]==len(tokens) and value==g[exp[lhs]]
  env[lhs]=value;seen.append(lhs)
 assert seen==list(exp);definition_counts[case['label']]=len(seen)
 equation=re.sub(r'\s+','',display.split('The single Diophantine equation is',1)[1])
 if case['label']=='sum87':
  assert equation==r'\[\boxed{\mathcal{P}^2+\mathcal{D}^2+\mathcal{Q}^2+\mathcal{R}^2=0.}\]'
 else:
  assert equation==r'\[\boxed{\begin{aligned}&[1+Z^2-M^2(1+\ell(\ell+k))]\\&\quad\cdot[1+D^2-U^2(1+\Delta c^2)]\\&\quad\cdot[\upsilon^2-Q(\upsilon^2-V^2)][1+I^2-Q]=1.\end{aligned}}\]'.replace(' ','')
  for txt,key in [('1+Z^2-M^2(1+\\ell(\\ell+k))','F0'),('1+D^2-U^2(1+\\Delta c^2)','F1'),
                  ('\\upsilon^2-Q(\\upsilon^2-V^2)','Fa'),('1+I^2-Q','Fs')]:
   tok=tokens_of(txt);pos=[0];assert expression(tok,env,pos)==g[key] and pos[0]==len(tok)
 local_rename=dict(rename)
 if case['label']=='product86':local_rename.update({'F0':'first','F1':'main','Fa':'aux','Fs':'strong','P13':'P'})
 local_fmt=lambda x:local_rename.get(str(x),str(x)).replace('_',r'\_')
 def check_gates(t):
  lines=[l for l in t.splitlines() if l[:1].isdigit() and '. ' in l and ' = ' in l and l.endswith(r'\\')]
  assert len(lines)==case['n']
  for i,(line,(n,op,a,b)) in enumerate(zip(lines,c['source']),1):
   want=f'{i}. {local_fmt(n)} = {local_fmt(a)} {op} {local_fmt(b)}'+r'\\';assert line==want,(case['label'],i,line,want)
 check_gates(text)
 for old,new in [('1. b = J * beta','1. b = J + beta'),('1. b = J * beta','1. b = F * beta')]:
  changed=text.replace(old,new,1);assert changed!=text
  try:check_gates(changed)
  except AssertionError:pass
  else:raise AssertionError('printed gate mutation accepted')
 assert block(text)==block(original.read_text())
 decimal=block(text).split(r'\selectfont\ttfamily',1)[1].split(end,1)[0].strip().splitlines()
 assert len(decimal)==12 and all(re.fullmatch(r'\d+\\par',l) for l in decimal)
 builds[case['label']]=[]
 with tempfile.TemporaryDirectory(prefix='frontier13-pdf-audit-') as tmp:
  for name in ('first','second'):
   dest=Path(tmp)/name;dest.mkdir();q=subprocess.run(['pdflatex','-halt-on-error','-interaction=batchmode','-output-directory',str(dest),str(case['tex'])],cwd=ROOT,text=True,capture_output=True,timeout=180)
   assert q.returncode==0,(q.stdout,q.stderr);builds[case['label']].append(H(dest/(case['tex'].stem+'.pdf')))
 assert builds[case['label']]==[H(case['pdf'])]*2

# The historical parent and the earlier independently repeated Lean port
# computation identify the same project provider and full coefficient bytes.
pair=J(REV/'fresh-project-pair-independent-audit/receipt.json');pt=J(REV/'fresh-project-pair-independent-audit/terminal-observation.json')
assert pair['status']=='PASS_INDEPENDENT_PAIRED_ARTIFACT_AUDIT' and pt['exit_code']==0 and pt['receipt_sha256']==H(REV/'fresh-project-pair-independent-audit/receipt.json')
assert H(SNAP/'manifest.json')==pair['manifest_sha256']
for label in ('author','peer'):
 assert H(PARENT/label/'state.json')==pair[label+'_state_sha256'];state=J(PARENT/label/'state.json')
 for name in ('AdaptiveDirectOrdinateSquareSums','AdaptiveDirectOrdinate86Literal','HAAdaptiveDirectOrdinate86'):
  row=next(r for r in state['records'] if r['module']=='DiophantineConsistency.'+name);assert row['exit']==0
  assert row['source_sha256']==H(SNAP/('src/DiophantineConsistency/'+name+'.lean'))
 kernel=next(r for r in state['records'] if r['module']=='DiophantineConsistency.CurrentKernelData2011')
 assert kernel['object_sha256']=='95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896'
prior=J(PR/'receipt.json');pt=J(PR/'terminal-observation.json');probe=J(PORT/'ports-receipt.json');printed=J(PORT/'printed-constants-repeat.json')
assert prior['status']=='PASS_INDEPENDENT_FINITE_BINDING_REVIEW' and pt['observed_exit_code']==0 and pt['receipt_sha256']==H(PR/'receipt.json')
assert prior['fresh_probe_exit']==prior['recipe_rerun_exit']==0 and probe['parent_state_sha256']==pair['author_state_sha256']
assert probe['kernel_data_object_sha256']==kernel['object_sha256'] and printed['constant_block_sha256']==raw(block(original.read_text()).encode())
matches=[v for p,v in prior['input_sha256'].items() if p.endswith('/reviews/equation14-historical-literal-binding/printed-constants-repeat.json')]
assert matches==[H(PORT/'printed-constants-repeat.json')]
ports=[]
for i,(name,shown) in enumerate(zip(ports_expected,['beta','K','MC','MF_source'])):
 meta=carrier['coefficient_binding']['ports'][name];packed=(COEFF/'coefficients'/meta['file']).read_bytes();assert raw(packed)==meta['gzip_sha256']
 binary=gzip.decompress(packed);dec=gzip.decompress((PORT/'port-outputs'/f'port{i}.txt.gz').read_bytes())
 assert raw(binary)==meta['raw_sha256']==printed['fixed_port_records'][shown]['sha256']==prior['ports'][i]['integer_sha256']
 def check_dec(d):assert d==str(int.from_bytes(binary,'big')).encode()
 check_dec(dec);assert raw(dec)==prior['ports'][i]['decimal_sha256']
 try:check_dec(bytes([dec[0]^1])+dec[1:])
 except AssertionError:pass
 else:raise AssertionError(('port mutation accepted',i))
 ports.append({'name':name,'integer_sha256':raw(binary),'decimal_sha256':raw(dec)})
assert {str(p.resolve()):H(p) for p in files}==before
result={'status':'PASS_FRONTIER13_FINITE_LEAN_PDF_BINDING','inputs_sha256':before,'ports':ports,
        'mutations':'Three Lean literal and two printed gate mutations per equation, plus four captured port-digit mutations',
        'cases':{c['label']:{'gates':c['n'],'variables':13,'definitions':definition_counts[c['label']],
                 'pdf_sha256':H(c['pdf']),'independent_build_sha256':builds[c['label']]} for c in cases},
        'scope':'Finite source/circuit/PDF checks and prior #eval comparisons; no new Lean endpoint replay or formal TeX semantics. Fixed decoder/table/rank recipe is manually transcribed.'}
out=D/'receipt.json';assert not out.exists();out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(result['status'],H(out))
