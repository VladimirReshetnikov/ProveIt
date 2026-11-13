#!/usr/bin/env python3
"""Independent finite audit of the historical direct14 literal and PDF."""
import gzip,hashlib,json,re,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
sys.set_int_max_str_digits(0)
D=Path(__file__).resolve().parent;ROOT=D.parents[1];REV=ROOT/'reviews'
RESEARCH=ROOT/'research/adaptive-square-sums14-direct';SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2')
PARENT=Path('/tmp/ipra-aq29-fresh-project-pair');PORT=REV/'equation14-historical-literal-binding'
PORT_REVIEW=REV/'equation14-historical-literal-binding-independent';COEFF=ROOT/'candidates/one-page-padding-staircase-carrier65-2011'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
raw=lambda b:hashlib.sha256(b).hexdigest();J=lambda p:json.loads(Path(p).read_text())
graph=RESEARCH/'candidate.json';tex=ROOT/'equation30-direct.tex';pdf=ROOT/'equation30-direct.pdf'
literal=SNAP/'src/DiophantineConsistency/AdaptiveSquareWitnessDirect14.lean'
endpoint=SNAP/'src/DiophantineConsistency/IPRASquareWitnessDirect14Native.lean'
files=[Path(__file__).resolve(),graph,tex,pdf,ROOT/'equation.tex',literal,endpoint,SNAP/'manifest.json',
       PARENT/'author/state.json',PARENT/'peer/state.json',REV/'fresh-project-pair-independent-audit/receipt.json',
       REV/'fresh-project-pair-independent-audit/terminal-observation.json',PORT/'ports-receipt.json',
       PORT/'printed-constants-repeat.json',PORT_REVIEW/'receipt.json',PORT_REVIEW/'terminal-observation.json',COEFF/'polynomial.json']
carrier=J(COEFF/'polynomial.json');files += [PORT/'port-outputs'/f'port{i}.txt.gz' for i in range(4)]
files += [COEFF/'coefficients'/carrier['coefficient_binding']['ports'][n]['file'] for n in carrier['fixed_numerals']]
before={str(p.resolve()):H(p) for p in files}
assert H(graph)=='bef34f7d0541766eea3c9a7a2abb90633e97e6df73c7b69011f195ced0f2d5b4'
c=J(graph);assert len(c['witnesses'])==14 and len(set(c['witnesses']))==14 and len(c['source'])==90
assert c['fixed_numerals']==carrier['fixed_numerals']==['beta','K0','MC','MF']

def check_literal(s):
 marker='def literal (p : Fin 4 → ℤ) : Expr (Fin 14) :=\n';assert s.count(marker)==1
 body=s.split(marker,1)[1].split('\ndef embed ',1)[0].splitlines()
 want=[f'  let {n} : Expr (Fin 14) := .var {i}' for i,n in enumerate(c['witnesses'])]
 want += [f'  let {n} : Expr (Fin 14) := .constant (p {i})' for i,n in enumerate(c['fixed_numerals'])]
 want += [f'  let {n} := {a} {op} {b}' for n,op,a,b in c['source']]
 want += ['  '+c['output']];assert body==want
ls=literal.read_text();check_literal(ls)
prefix,body=ls.split('def literal (p : Fin 4 → ℤ) : Expr (Fin 14) :=\n',1)
for old,new in [('.var 0','.var 1'),('.constant (p 0)','.constant (p 1)'),
                ('let qm := J * beta','let qm := J + beta'),('let qm := J * beta','let qm := F * beta')]:
 mutated=body.replace(old,new,1);assert mutated!=body
 t=prefix+'def literal (p : Fin 4 → ℤ) : Expr (Fin 14) :=\n'+mutated
 try:check_literal(t)
 except AssertionError:pass
 else:raise AssertionError('literal mutation accepted')
assert 'positiveShift\n  (AdaptiveSquareWitnessDirect14.literal CurrentWindowCarry2011.ports)' in endpoint.read_text()
assert '∼mappedNativeRefutation embedding' in endpoint.read_text()

# Independent sparse integer-polynomial evaluation and a small parser for the
# 25 displayed arithmetic definitions. This is not a general TeX parser.
names=c['witnesses']+c['fixed_numerals'];zero=(0,)*len(names)
def lift(n):return {} if n==0 else {zero:n}
def add(a,b,sign=1):
 out=a.copy()
 for k,v in b.items():out[k]=out.get(k,0)+sign*v
 return {k:v for k,v in out.items() if v}
def mul(a,b):
 out={}
 for ka,va in a.items():
  for kb,vb in b.items():
   k=tuple(x+y for x,y in zip(ka,kb));out[k]=out.get(k,0)+va*vb
 return {k:v for k,v in out.items() if v}
g={}
for i,n in enumerate(names):
 k=list(zero);k[i]=1;g[n]={tuple(k):1}
skip={'firstSquare','mainSquare','auxSquare','strongSquare','firstMain','firstMainAux','sumSquares','squareConstraint','sumWithConstraint'}
for target,op,a,b in c['source']:
 if target in skip:continue
 x=lift(a) if isinstance(a,int) else g[a];y=lift(b) if isinstance(b,int) else g[b]
 g[target]=add(x,y) if op=='+' else add(x,y,-1) if op=='-' else mul(x,y)
symbol={'J':'J','F':'F','alpha':'alpha','f':'f','g':'i','T':'T','X':'X','Y':'Y','xi':'r','eta':'eta',
        'zeta':'zeta','upsilon':'y','gamma':'gamma','vartheta':'squareVariable',
        'beta':'beta','K':'K0','mu':'MC','omega':'MF'}
expected={'b':'qm','q':'q','C':'C','U':'U','E':'E','k':'k','ell':'ell','c':'c','a':'a','H':'H',
          'Delta':'Delta','L':'b0','M':'M','W':'Bt','R':'R','Z':'Z','D':'Dstar','I':'I','Q':'Q','V':'V',
          '@P':'A0','@D':'A1','@Q':'auxResidual','@R':'g72','@E':'squareDifference'}
token=re.compile(r'\\[A-Za-z]+|@[PDQRE]|[A-Za-z]|[0-9]+|[+\-^=()\[\]]')
def parse_defs(text):
 display=text.split('% BEGIN VERIFIED DISPLAY\n',1)[1].split('% END VERIFIED DISPLAY',1)[0]
 u=re.search(r'variables\s*\\\[(.*?)\\in\\mathbb Z_\{>0\}\.\s*\\\]',display,re.S);assert u
 assert [x.strip().lstrip('\\') for x in u[1].split(',')]==['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma','vartheta']
 eq=display.split('The single Diophantine equation is',1)[1]
 assert re.sub(r'\s+','',eq)==r'\[\boxed{\mathcal{P}^2+\mathcal{D}^2+\mathcal{Q}^2+\mathcal{R}^2+\mathcal{E}^2=0.}\]'
 body=re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}',display,re.S)[1]
 body=body.replace('\\\\',',').replace(r'\quad','').strip();assert body.endswith('.')
 for ch in 'PDQRE':body=body.replace('\\mathcal{'+ch+'}','@'+ch)
 env={k:g[v] for k,v in symbol.items()};seen=[]
 for definition in (x for x in body[:-1].split(',') if x.strip()):
  compact=re.sub(r'\s+','',definition);tokens=token.findall(definition);assert ''.join(tokens)==compact
  tokens=[x[1:] if x.startswith('\\') else x for x in tokens];pos=0
  def peek():return tokens[pos] if pos<len(tokens) else None
  def atom():
   nonlocal pos
   t=peek();assert t is not None;pos+=1
   if t in ('(', '['):
    val=expr();assert peek()==(')' if t=='(' else ']');pos+=1
   elif t.isdecimal():val=lift(int(t))
   else:assert t in env,(definition,t);val=env[t]
   if peek()=='^':
    pos+=1;n=peek();assert n is not None and n.isdecimal() and 0<=int(n)<=3;pos+=1
    base=val;val=lift(1)
    for _ in range(int(n)):val=mul(val,base)
   return val
  def product():
   val=atom()
   while peek() is not None and peek() not in ('+', '-', ')',']','='):
    val=mul(val,atom())
   return val
  def expr():
   nonlocal pos
   val=product()
   while peek() in ('+','-'):
    op=peek();pos+=1;val=add(val,product(),1 if op=='+' else -1)
   return val
  lhs=tokens[0];assert lhs in expected and lhs not in seen and tokens[1]=='='
  pos=2;value=expr();assert pos==len(tokens) and value==g[expected[lhs]]
  env[lhs]=value;seen.append(lhs)
 assert seen==list(expected)
parse_defs(tex.read_text())

rename={'r':'xi','i':'g','y':'upsilon','K0':'K','MC':'mu','MF':'omega','qm':'b','Bt':'W','b0':'L',
        'Dstar':'D','G':'rankseed','squareVariable':'vartheta','squareConstraint':'constraint',
        'squareDifference':'difference','sumWithConstraint':'result'}
fmt=lambda x:rename.get(str(x),str(x)).replace('_',r'\_')
def check_gates(text):
 lines=[line for line in text.splitlines() if line[:1].isdigit() and '. ' in line and ' = ' in line and line.endswith(r'\\')]
 assert len(lines)==90
 for i,(line,(n,op,a,b)) in enumerate(zip(lines,c['source']),1):assert line==f'{i}. {fmt(n)} = {fmt(a)} {op} {fmt(b)}'+r'\\'
check_gates(tex.read_text())
for old,new in [('M=q^3b','M=q^2b'),(r'\vartheta-V^2',r'\vartheta+V^2')]:
 t=tex.read_text().replace(old,new,1);assert t!=tex.read_text()
 try:parse_defs(t)
 except AssertionError:pass
 else:raise AssertionError('display mutation accepted')
for old,new in [('1. b = J * beta', '1. b = J + beta'),('1. b = J * beta', '1. b = F * beta')]:
 t=tex.read_text().replace(old,new,1);assert t!=tex.read_text()
 try:check_gates(t)
 except AssertionError:pass
 else:raise AssertionError('gate mutation accepted')

begin=r'\textbf{The four fixed integers.}';end=r'\endgroup'
def block(t):
 i=t.index(begin);return t[i:t.index(end,t.index(r'\textbf{The integer $\mathcal A$',i))+len(end)]
assert block(tex.read_text())==block((ROOT/'equation.tex').read_text())
assert raw(block(tex.read_text()).encode())=='e5e7b58b54e57badc97ba6ee7f7577ec8e858c88189474723ce28ae629b0a6c6'
decimal=block(tex.read_text()).split(r'\selectfont\ttfamily',1)[1].split(end,1)[0].strip().splitlines()
assert len(decimal)==12 and all(re.fullmatch(r'\d+\\par',line) for line in decimal)

# Connect the matched historical parent to the same #eval provider and the
# previously checked, manually transcribed printed-constant reconstruction.
pair=J(REV/'fresh-project-pair-independent-audit/receipt.json');pt=J(REV/'fresh-project-pair-independent-audit/terminal-observation.json')
assert pair['status']=='PASS_INDEPENDENT_PAIRED_ARTIFACT_AUDIT' and pt['exit_code']==0 and pt['receipt_sha256']==H(REV/'fresh-project-pair-independent-audit/receipt.json')
assert H(SNAP/'manifest.json')==pair['manifest_sha256']
for label in ('author','peer'):
 assert H(PARENT/label/'state.json')==pair[label+'_state_sha256']
 state=J(PARENT/label/'state.json')
 for module,path in [('AdaptiveSquareWitnessDirect14',literal),('IPRASquareWitnessDirect14Native',endpoint)]:
  row=next(x for x in state['records'] if x['module']=='DiophantineConsistency.'+module)
  assert row['exit']==0 and row['source_sha256']==H(path) and not row['axiom_reports']
 kernel=next(x for x in state['records'] if x['module']=='DiophantineConsistency.CurrentKernelData2011')
 assert kernel['object_sha256']=='95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896'
prior=J(PORT_REVIEW/'receipt.json');pt=J(PORT_REVIEW/'terminal-observation.json');probe=J(PORT/'ports-receipt.json');printed=J(PORT/'printed-constants-repeat.json')
assert prior['status']=='PASS_INDEPENDENT_FINITE_BINDING_REVIEW' and pt['observed_exit_code']==0 and pt['receipt_sha256']==H(PORT_REVIEW/'receipt.json')
assert prior['fresh_probe_exit']==prior['recipe_rerun_exit']==0
matches=[h for p,h in prior['input_sha256'].items() if p.endswith('/reviews/equation14-historical-literal-binding/printed-constants-repeat.json')]
assert matches==[H(PORT/'printed-constants-repeat.json')]
assert prior['input_sha256'][str((PARENT/'author/state.json').resolve())]==pair['author_state_sha256']
assert probe['parent_state_sha256']==pair['author_state_sha256'] and probe['kernel_data_object_sha256']==kernel['object_sha256']
assert printed['constant_block_sha256']=='e5e7b58b54e57badc97ba6ee7f7577ec8e858c88189474723ce28ae629b0a6c6'
ports=[]
def check_decimal_port(decimal,binary):
 assert decimal==str(int.from_bytes(binary,'big')).encode()
for i,(name,shown) in enumerate(zip(c['fixed_numerals'],['beta','K','MC','MF_source'])):
 meta=carrier['coefficient_binding']['ports'][name];data=(COEFF/'coefficients'/meta['file']).read_bytes();assert raw(data)==meta['gzip_sha256']
 binary=gzip.decompress(data);decimal=gzip.decompress((PORT/'port-outputs'/f'port{i}.txt.gz').read_bytes())
 assert raw(binary)==meta['raw_sha256']==printed['fixed_port_records'][shown]['sha256']==prior['ports'][i]['integer_sha256']
 check_decimal_port(decimal,binary);assert raw(decimal)==prior['ports'][i]['decimal_sha256']
 mutated=bytes([decimal[0]^1])+decimal[1:]
 try:check_decimal_port(mutated,binary)
 except AssertionError:pass
 else:raise AssertionError(('port mutation accepted',i))
 ports.append({'name':name,'integer_sha256':raw(binary),'decimal_sha256':raw(decimal),'decimal_digits':len(decimal)})

builds=[]
with tempfile.TemporaryDirectory(prefix='direct14-display-audit-') as tmp:
 for name in ('one','two'):
  dest=Path(tmp)/name;dest.mkdir()
  q=subprocess.run(['pdflatex','-halt-on-error','-interaction=batchmode','-output-directory',str(dest),str(tex)],cwd=ROOT,text=True,capture_output=True,timeout=180)
  assert q.returncode==0,(q.stdout,q.stderr)
  builds.append(H(dest/'equation30-direct.pdf'))
assert builds==[H(pdf),H(pdf)]
assert {str(p.resolve()):H(p) for p in files}==before
result={'status':'PASS_DIRECT14_FINITE_LEAN_PDF_BINDING','inputs_sha256':before,'variables':14,'ports':ports,
        'lean_and_printed_gates':90,'parsed_definitions':25,'residuals':5,'pdf_sha256':H(pdf),
        'independent_build_sha256':builds,'mutations':['variable_index','port_index','lean_op','lean_operand','formula_power','formula_sign','gate_op','gate_operand','four_port_decimal_digits'],
        'scope':'Finite historical source/circuit/PDF binding and recorded #eval comparisons. No new Lean endpoint replay or formal TeX/PDF semantics; decoder/table/rank recipes remain manually transcribed.'}
out=D/'receipt.json';assert not out.exists();out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(result['status'],H(out),H(pdf))
