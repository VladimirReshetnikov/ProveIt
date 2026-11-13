#!/usr/bin/env python3
"""Independent finite audit of the AQ17 printed circuit."""
import hashlib,json,re,shutil,subprocess,sys,tempfile
from collections import Counter
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];D=ROOT/'research/aq22-positive-binding-survey'
G=D/'candidate17.json';T=D/'equation32-17.tex';PDF=D/'equation32-17.pdf';GEN=D/'build_display17.py';ORIG=ROOT/'equation.tex'
OBS=ROOT/'research/aq17-witness-transport/exploratory/observations.json';CERT=ROOT/'reviews/aq17-candidate-independent-audit/receipt.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_text())
inputs=[Path(__file__),G,T,PDF,GEN,ORIG,OBS,CERT]
before={str(p.resolve()):H(p) for p in inputs}
assert H(G)=='760b9e7babbb559b7175344915456fdc3d9bd8ce85382873d4915faf2cd76d81'
c=J(G);cert=J(CERT);obs=J(OBS)
assert cert['status']=='PASS_AQ17_INDEPENDENT_FINITE_AUDIT' and cert['variables']==17 and cert['gates']==99 and cert['total_degree']==32
assert cert['inputs_sha256'][str(G.resolve())]==H(G)
assert obs['candidate_sha256']==H(G) and obs['literal_binding_check']['observed_exit_code']==0
modules={x['module']:x for x in obs['rows']}
assert {'AdaptiveAQ17Transport','AdaptiveAQ17','IPRAAQ17Native','IPRAStandardAQ17'}<=set(modules)
assert all(modules[n]['observed_exit_code']==0 for n in ('AdaptiveAQ17Transport','AdaptiveAQ17','IPRAAQ17Native','IPRAStandardAQ17'))
witness=['J','F','alpha','f','i','T','X','Y','r','eta','zeta','y','gamma','rankVariable','zValueVariable','dValueVariable','vValueVariable']
names=['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma','epsilon','Z','D','V']
ports=['beta','K0','MC','MF'];port_names=['beta','K','mu','omega']
assert c['witnesses']==witness and c['fixed_numerals']==ports
assert len(set(names+port_names))==21
text=T.read_text();assert r'\boxed{\texttt{hCU}=0.}' in text
assert r'\begin{gathered}J,F,\alpha,f,g,T,X,Y,\xi,\eta,\zeta,\upsilon,\gamma,\epsilon,Z,D,V\in\mathbb Z_{>0}.\end{gathered}' in text
ascii_names=re.search(r'Their ASCII names in the circuit are respectively\s*\\texttt\{(.*?)\}',text,re.S)
assert ascii_names and [x.strip() for x in ascii_names[1].replace('\n',' ').split(',')]==names
assert 'The four fixed integers are \\texttt{beta}, \\texttt{K}, \\texttt{mu}, and\n\\texttt{omega}' in text
assert 'An exploratory Lean run compiled witness transport\nand an intuitionistic PRA equivalence to a translated consistency sentence;\na guarded replay remains pending.' in text
assert 'No\nminimality claim is made.' in text
# Name mapping and complete circuit comparison independently of the generator.
def gate(i):
    out=''
    while i:i,r=divmod(i-1,26);out=chr(65+r)+out
    return 'h'+out
mapping=dict(zip(witness+ports,names+port_names));rows={};available=set(mapping)
for i,(name,op,a,b) in enumerate(c['source'],1):
    assert name not in available and op in ('+','-','*')
    assert all(isinstance(x,int) or x in available for x in (a,b))
    available.add(name);rows[name]=(op,a,b);mapping[name]=gate(i)
assert len(rows)==99 and len(set(mapping.values()))==len(mapping) and mapping[c['output']]=='hCU'
body=text.split('% BEGIN CIRCUIT\n',1)[1].split('\n% END CIRCUIT',1)[0].splitlines()
def lines_ok(lines):
    assert len(lines)==99
    for i,(entry,line) in enumerate(zip(c['source'],lines),1):
        name,op,a,b=entry
        m=re.fullmatch(r'(\d+)\. ([A-Za-z]+) = ([A-Za-z]+|\d+) ([+*\-]) ([A-Za-z]+|\d+)\\\\',line);assert m
        shown=lambda x:str(x) if isinstance(x,int) else mapping[x]
        assert (int(m[1]),m[2],m[3],m[4],m[5])==(i,mapping[name],shown(a),op,shown(b)),i
lines_ok(body)
live=set();todo=[c['output']]
while todo:
    name=todo.pop()
    if not isinstance(name,str) or name in live:continue
    live.add(name)
    if name in rows:todo.extend(rows[name][1:])
assert set(rows)|set(witness+ports)<=live

def squares(node):
    op,a,b=rows[node]
    if op=='+':return squares(a)+squares(b)
    assert op=='*' and a==b and a in c['residuals'];return [a]
assert Counter(squares(c['output']))==Counter(c['residuals']) and len(c['residuals'])==8
# Check exact inherited fixed block and printed decimal text, without claiming
# a general interpretation of TeX's table/decoder/rank recipe.
def fixed(s):
    begin=s.index(r'\textbf{The four fixed integers.}');end=s.index(r'\endgroup',s.index(r'\textbf{The integer $\mathcal A$',begin))+len(r'\endgroup')
    return s[begin:end]
block=fixed(text);assert block==fixed(ORIG.read_text())
assert hashlib.sha256(block.encode()).hexdigest()=='e5e7b58b54e57badc97ba6ee7f7577ec8e858c88189474723ce28ae629b0a6c6'
decimal=block.split(r'\selectfont\ttfamily',1)[1].split(r'\endgroup',1)[0].strip().splitlines()
assert len(decimal)==12 and all(re.fullmatch(r'\d+\\par',line) for line in decimal)
assert 'base 10' in text and len(''.join(line[:-4] for line in decimal))>600
for label,changed in [('operation',body[0].replace(' * ',' + ')),('operand',body[0].replace('J *','F *')),('target',body[0].replace('hA =','hB ='))]:
    trial=body.copy();trial[0]=changed;assert trial!=body
    try:lines_ok(trial)
    except AssertionError:pass
    else:raise AssertionError(('mutation accepted',label))
def check_fixed(t):assert fixed(t)==fixed(ORIG.read_text())
changed=text.replace(decimal[0],decimal[0].replace('1','2',1),1);assert changed!=text
try:check_fixed(changed)
except AssertionError:pass
else:raise AssertionError('decimal mutation accepted')
def check_names(values):assert len(set(values))==17 and values==names
duplicated=names.copy();duplicated[1]=duplicated[0]
try:check_names(duplicated)
except AssertionError:pass
else:raise AssertionError('duplicate input mutation accepted')
# Run the generator in an isolated tree and additionally compile the exact
# maintained TeX twice in clean directories.
with tempfile.TemporaryDirectory(prefix='aq17-display-audit-') as td:
    root=Path(td);d=root/'research/aq22-positive-binding-survey';d.mkdir(parents=True)
    for p in (GEN,G):shutil.copy2(p,d/p.name)
    shutil.copy2(ORIG,root/'equation.tex')
    q=subprocess.run([sys.executable,str(d/GEN.name)],cwd=d,text=True,capture_output=True,timeout=180)
    assert q.returncode==0,(q.stdout,q.stderr)
    assert (d/T.name).read_bytes()==T.read_bytes() and (d/PDF.name).read_bytes()==PDF.read_bytes()
    builds=[]
    for name in ('first','second'):
        out=root/name;out.mkdir()
        p=subprocess.run(['pdflatex','-halt-on-error','-interaction=batchmode','-output-directory',str(out),T.name],cwd=d,text=True,capture_output=True,timeout=180)
        assert p.returncode==0,(p.stdout,p.stderr)
        log=(out/'equation32-17.log').read_text(errors='replace');assert not re.search(r'overfull|underfull|warning',log,re.I)
        builds.append(H(out/PDF.name))
    assert builds==[H(PDF),H(PDF)]
info=subprocess.run(['pdfinfo',str(PDF)],text=True,capture_output=True,check=True).stdout
assert re.search(r'^Pages:\s+2\s*$',info,re.M)
for page in (1,2):
    extracted=subprocess.run(['pdftotext','-layout','-f',str(page),'-l',str(page),str(PDF),'-'],text=True,capture_output=True,check=True).stdout
    assert len(extracted)>500 and ('seventeen-variable' in extracted if page==1 else '99-operation circuit' in extracted)
assert {str(p.resolve()):H(p) for p in inputs}==before
result={'status':'PASS_INDEPENDENT_AQ17_DISPLAY','inputs_sha256':before,'variables':17,'ports':4,'operations':99,'squares':8,
 'pdf_pages':2,'pdf_sha256':H(PDF),'clean_build_sha256':builds,
 'mutation_controls':['operation','operand','target','decimal_digit','duplicate_variable'],
 'scope':'Finite graph/display and reproducibility check, exploratory Lean observations only. Manual TeX decoder/rank recipe; no formal PDF-to-Lean binding, guarded AQ17 replay or global minimality claim.'}
out=HERE/'receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out),H(PDF))
