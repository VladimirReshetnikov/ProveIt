#!/usr/bin/env python3
"""Independent review and detached rerun of the two 13-variable PDF bindings."""
import gzip,hashlib,json,re,shutil,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];REV=ROOT/'reviews';ORIG=REV/'frontier13-pdf-historical-lean-binding'
PARENT=Path('/tmp/ipra-aq29-fresh-project-pair');SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2');PORT=REV/'equation14-historical-literal-binding';PORT_REVIEW=REV/'equation14-historical-literal-binding-independent';COEFF=ROOT/'candidates/one-page-padding-staircase-carrier65-2011'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());digest=lambda b:hashlib.sha256(b).hexdigest()
prior=J(ORIG/'receipt.json');terminal=J(ORIG/'terminal-observation.json');pair=J(REV/'fresh-project-pair-independent-audit/receipt.json')
assert prior['status']=='PASS_FRONTIER13_FINITE_LEAN_PDF_BINDING' and terminal['ordinary_python_exit_code']==0
assert pair['status']=='PASS_INDEPENDENT_PAIRED_ARTIFACT_AUDIT' and J(REV/'fresh-project-pair-independent-audit/terminal-observation.json')['exit_code']==0
cases=[('sum87',ROOT/'research/adaptive-square-sums/candidate.json',ROOT/'equation36.tex',ROOT/'equation36.pdf',87,'11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828'),
       ('product86',ROOT/'research/adaptive-direct-ordinate86/candidate.json',ROOT/'equation86.tex',ROOT/'equation86.pdf',86,'e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f')]
inputs=[Path(__file__),ORIG/'audit.py',ORIG/'receipt.json',ORIG/'terminal-observation.json',ROOT/'equation.tex',SNAP/'manifest.json',PARENT/'author/state.json',PARENT/'peer/state.json',REV/'fresh-project-pair-independent-audit/receipt.json',PORT_REVIEW/'receipt.json',PORT_REVIEW/'terminal-observation.json',PORT/'printed-constants-repeat.json',COEFF/'polynomial.json']
for _,g,t,p,_,_ in cases:inputs.extend((g,t,p))
carrier=J(COEFF/'polynomial.json')
for i,name in enumerate(carrier['fixed_numerals']):inputs.extend((PORT/'port-outputs'/f'port{i}.txt.gz',COEFF/'coefficients'/carrier['coefficient_binding']['ports'][name]['file']))
before={str(p.resolve()):H(p) for p in inputs}
assert H(ORIG/'audit.py')==prior['inputs_sha256'][str((ORIG/'audit.py').resolve())]
assert H(SNAP/'manifest.json')==pair['manifest_sha256']
for label in ('author','peer'):
 assert H(PARENT/label/'state.json')==pair[label+'_state_sha256']
 state=J(PARENT/label/'state.json');kernel=next(r for r in state['records'] if r['module']=='DiophantineConsistency.CurrentKernelData2011')
 assert kernel['object_sha256']=='95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896'
# Check the complete numbered gate lines and all input/port names separately
# from the original packet's TeX-expression parser.
witness=['J','F','alpha','f','i','T','X','Y','r','eta','zeta','y','gamma'];ports=['beta','K0','MC','MF']
rename={'r':'xi','i':'g','y':'upsilon','K0':'K','MC':'mu','MF':'omega','qm':'b','Bt':'W','b0':'L','Dstar':'D','G':'rankseed'}
fixed_start=r'\textbf{The four fixed integers.}';fixed_end=r'\endgroup'
def block(t):
 i=t.index(fixed_start);return t[i:t.index(fixed_end,t.index(r'\textbf{The integer $\mathcal A$',i))+len(fixed_end)]
fixed=block((ROOT/'equation.tex').read_text());assert digest(fixed.encode())=='e5e7b58b54e57badc97ba6ee7f7577ec8e858c88189474723ce28ae629b0a6c6'
for label,g,t,p,count,pin in cases:
 assert H(g)==pin;graph=J(g);text=t.read_text();assert graph['witnesses']==witness and graph['fixed_numerals']==ports
 assert len(graph['source'])==count and block(text)==fixed
 display=text.split('% BEGIN VERIFIED DISPLAY\n',1)[1].split('% END VERIFIED DISPLAY',1)[0]
 unknowns=re.search(r'variables\s*\\\[(.*?)\\in\\mathbb Z_\{>0\}\.\s*\\\]',display,re.S);assert unknowns
 assert [x.strip().lstrip('\\') for x in unknowns[1].split(',')]==['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma']
 alias=dict(rename)
 if label=='product86':alias.update({'F0':'first','F1':'main','Fa':'aux','Fs':'strong','P13':'P'})
 def fmt(x):return alias.get(str(x),str(x)).replace('_',r'\_')
 lines=[x for x in text.splitlines() if x[:1].isdigit() and '. ' in x and ' = ' in x and x.endswith(r'\\')]
 assert len(lines)==count
 for i,(line,(name,op,left,right)) in enumerate(zip(lines,graph['source']),1):
  assert line==f'{i}. {fmt(name)} = {fmt(left)} {op} {fmt(right)}'+r'\\',(label,i)
 equation=re.sub(r'\s+','',display.split('The single Diophantine equation is',1)[1])
 if label=='sum87':assert equation==r'\[\boxed{\mathcal{P}^2+\mathcal{D}^2+\mathcal{Q}^2+\mathcal{R}^2=0.}\]'
 else:assert equation==r'\[\boxed{\begin{aligned}&[1+Z^2-M^2(1+\ell(\ell+k))]\\&\quad\cdot[1+D^2-U^2(1+\Delta c^2)]\\&\quad\cdot[\upsilon^2-Q(\upsilon^2-V^2)][1+I^2-Q]=1.\end{aligned}}\]'.replace(' ','')
 assert prior['cases'][label]['gates']==count and prior['cases'][label]['pdf_sha256']==H(p)
# Independently recompare all digits against coefficient bytes and the
# independently repeated historical #eval evidence.
pr=J(PORT_REVIEW/'receipt.json');pt=J(PORT_REVIEW/'terminal-observation.json');assert pr['status']=='PASS_INDEPENDENT_FINITE_BINDING_REVIEW' and pt['observed_exit_code']==0
assert pr['fresh_probe_exit']==0 and pr['recipe_rerun_exit']==0
ports_checked=[]
for i,name in enumerate(ports):
 meta=carrier['coefficient_binding']['ports'][name];packed=(COEFF/'coefficients'/meta['file']).read_bytes();binary=gzip.decompress(packed);decimal=gzip.decompress((PORT/'port-outputs'/f'port{i}.txt.gz').read_bytes())
 assert digest(packed)==meta['gzip_sha256'] and digest(binary)==meta['raw_sha256']==pr['ports'][i]['integer_sha256']
 assert decimal==str(int.from_bytes(binary,'big')).encode() and digest(decimal)==pr['ports'][i]['decimal_sha256']
 ports_checked.append({'name':name,'integer_sha256':digest(binary),'decimal_sha256':digest(decimal)})
# Detached rerun preserves the original packet. Its stronger TeX parser,
# all mutations and clean PDF builds run without editing the source receipt.
with tempfile.TemporaryDirectory(prefix='frontier13-independent-repeat-',dir=REV) as td:
 d=Path(td);shutil.copy2(ORIG/'audit.py',d/'audit.py');assert H(d/'audit.py')==H(ORIG/'audit.py')
 run=subprocess.run([sys.executable,str(d/'audit.py')],capture_output=True,text=True,timeout=180)
 assert run.returncode==0,(run.stdout,run.stderr);new=J(d/'receipt.json')
 for key in ('status','ports','mutations','cases'):assert new[key]==prior[key],key
 optimized=[]
 for flag in ('-O','-OO'):
  bad=subprocess.run([sys.executable,flag,str(d/'audit.py')],capture_output=True,text=True,timeout=30)
  assert bad.returncode!=0 and 'optimized Python is unsupported' in bad.stderr
  optimized.append({'flag':flag,'exit_code':bad.returncode})
 detached={'exit_code':run.returncode,'stdout':run.stdout,'stderr':run.stderr,'receipt_sha256':H(d/'receipt.json'),'optimized':optimized}
assert {str(p.resolve()):H(p) for p in inputs}==before
result={'status':'PASS_INDEPENDENT_FRONTIER13_PDF_BINDING_REVIEW','inputs_sha256':before,'ports':ports_checked,'detached_original':detached,
        'cases':prior['cases'],'scope':'Finite graph/display and recorded-port review; no new Lean replay, guarded extension, or formal PDF semantics. Fixed decoder/table/rank/port recipe remains manually transcribed.'}
out=HERE/'receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out))
