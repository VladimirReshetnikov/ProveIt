#!/usr/bin/env python3
"""Independent finite audit of the 22-variable circuit-only presentation."""
import hashlib, json, os, re, shutil, subprocess, sys, tempfile
from pathlib import Path

if not __debug__:
    raise RuntimeError('optimized Python is unsupported')

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DIR = ROOT / 'research/adaptive-square-sums22-degree10'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
tex, pdf, graph = DIR/'equation10-22.tex', DIR/'equation10-22.pdf', DIR/'candidate.json'
generator, original = DIR/'build_display.py', ROOT/'equation.tex'
prior = ROOT/'reviews/aq22-degree10-independent-audit/receipt.json'
inputs = [Path(__file__).resolve(), tex, pdf, graph, generator, original, prior]
before = {str(x.resolve()): H(x) for x in inputs}
assert H(graph) == '1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106'
c = json.loads(graph.read_text())
cert = json.loads(prior.read_text())
assert cert['status'] == 'PASS_INDEPENDENT_AQ22_FINITE_AUDIT'
assert cert['child_sha256'] == H(graph) and cert['coordinates'] == 22
assert cert['operations'] == 114 and cert['child_residuals'] == 13
assert cert['leading_coefficient'] == -1 and max(cert['residual_degrees'].values()) == 5

# Bind every mathematical input by explicit position, independently of the
# presentation generator's own dictionary. PR code identifiers remain distinct.
witnesses = ['J','F','alpha','f','i','T','X','Y','r','eta','zeta','y','gamma',
             'scaleVariable','mainScaleVariable','rankVariable','ellVariable',
             'cSquareVariable','zValueVariable','dValueVariable','vValueVariable','deltaVariable']
names = ['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma',
         'psi','varphi','epsilon','ell','n','Z','D','V','delta']
ports, port_names = ['beta','K0','MC','MF'], ['beta','K','mu','omega']
assert c['witnesses'] == witnesses and c['fixed_numerals'] == ports
assert len(set(names)) == 22 and len(set(names + port_names)) == 26
text = tex.read_text()
assert r'\boxed{\texttt{hDJ}=0.}' in text
assert 'A Lean witness-transport theorem and an internal' in text
assert 'intuitionistic PRA equivalence for this candidate have not been proved.' in text
assert 'No\nminimality claim is made.' in text
unknown = re.search(r'\\begin\{gathered\}(J,F,\\alpha,.*?)\\in\\mathbb Z_\{>0\}\.\\end\{gathered\}', text, re.S)
assert unknown
actual = unknown.group(1).replace('\\\\','').replace('\n','').replace(' ','')
def check_unknown(s):
    assert s == r'J,F,\alpha,f,g,T,X,Y,\xi,\eta,\zeta,\upsilon,\gamma,\psi,\varphi,\epsilon,\ell,n,Z,D,V,\delta'
check_unknown(actual)
ascii_inputs = re.search(r'Their ASCII names in the circuit are respectively\s*\\texttt\{(.*?)\}', text, re.S)
assert ascii_inputs and [x.strip() for x in ascii_inputs.group(1).replace('\n',' ').split(',')] == names

def label(i):
    out = ''
    while i:
        i, r = divmod(i-1, 26)
        out = chr(65+r) + out
    return 'h'+out

rows = c['source']
alias = dict(zip(witnesses+ports, names+port_names))
mapping = dict(alias)
known = set(mapping)
table = {}
for i,(target,op,left,right) in enumerate(rows, 1):
    assert target not in known and op in ('+','-','*')
    assert all(isinstance(x,int) or x in known for x in (left,right))
    known.add(target); table[target] = (op,left,right); mapping[target] = label(i)
assert len(rows) == c['operations'] == 114 and mapping[c['output']] == 'hDJ'
assert len(set(mapping.values())) == len(mapping)
body = text.split('% BEGIN CIRCUIT\n',1)[1].split('\n% END CIRCUIT',1)[0].splitlines()
def check_lines(lines):
    assert len(lines) == len(rows)
    for i, ((target,op,left,right),line) in enumerate(zip(rows, lines), 1):
        m = re.fullmatch(r'(\d+)\. ([A-Za-z]+) = ([A-Za-z]+|\d+) ([+*\-]) ([A-Za-z]+|\d+)\\\\',line)
        assert m, ('syntax',i,line)
        shown = lambda v: str(v) if isinstance(v,int) else mapping[v]
        assert (int(m[1]),m[2],m[3],m[4],m[5]) == (i,mapping[target],shown(left),op,shown(right)), ('row',i)
check_lines(body)

# Derive topology/liveness and the 13 squares directly from the graph's output.
live={c['output']}; todo=list(live)
while todo:
    v=todo.pop()
    if v in table:
        for child in table[v][1:]:
            if isinstance(child,str) and child not in live:
                live.add(child); todo.append(child)
assert set(table) | set(witnesses+ports) <= live
def squares(v):
    op,a,b=table[v]
    if op=='*':
        assert a==b and isinstance(a,str)
        return [a]
    assert op=='+' and isinstance(a,str) and isinstance(b,str)
    return squares(a)+squares(b)
factors=squares(c['output'])
assert len(factors)==len(set(factors))==13 and 'g72' in factors
assert table['g72']==('-', 'g71','QComputed') and table['g71']==('*','I','I')
assert table['I']==('*','cSquareVariable','i')

# The constant text and decimal digits exactly match the maintained base-10
# source. Their decoder/rank interpretation is inherited, not parsed here.
source = original.read_text()
begin = r'\textbf{The four fixed integers.}'
endmark = r'\endgroup'
def fixed(t):
    start=t.index(begin); finish=t.index(endmark,t.index(r'\textbf{The integer $\mathcal A$',start))+len(endmark)
    return t[start:finish]
constants = fixed(text)
assert constants == fixed(source)
assert hashlib.sha256(constants.encode()).hexdigest()=='e5e7b58b54e57badc97ba6ee7f7577ec8e858c88189474723ce28ae629b0a6c6'
decimal = constants.split(r'\selectfont\ttfamily',1)[1].split(endmark,1)[0].strip().splitlines()
assert len(decimal)==12 and all(re.fullmatch(r'\d+\\par',line) for line in decimal)
assert 'base 10' in constants and len(''.join(x[:-4] for x in decimal)) > 600

# Mutations exercise our checker independently, including reordered input and
# circuit mismatches. Fixed text and status mutations are checked separately.
for label_,changed in [('operation', body[0].replace(' * ',' + ')),
                       ('operand',body[0].replace('J *','F *')),
                       ('target',body[0].replace('hA =','hB ='))]:
    trial=body.copy();trial[0]=changed
    try: check_lines(trial)
    except AssertionError: pass
    else: raise AssertionError(('mutation not detected',label_))
def check_constants(t):
    assert fixed(t) == fixed(source)
for label_, probe in [('decimal_digit', lambda: check_constants(text.replace(decimal[0],decimal[0].replace('1','2',1),1))),
                      ('unknown_duplicate', lambda: check_unknown(actual.replace('J,F,','J,J,',1)))]:
    try: probe()
    except AssertionError: pass
    else: raise AssertionError(('mutation not detected',label_))

# Recreate the full TeX and two clean PDFs in an isolated tree, using the
# author's generator only as a reproducibility check, not as this audit's
# graph or interface oracle.
with tempfile.TemporaryDirectory(prefix='aq22-display-independent-') as t:
    root=Path(t); d=root/'research/adaptive-square-sums22-degree10'; d.mkdir(parents=True)
    for p in (generator,graph): shutil.copy2(p,d/p.name)
    shutil.copy2(original,root/'equation.tex')
    q=subprocess.run([sys.executable,str(d/'build_display.py')],cwd=d,text=True,capture_output=True,timeout=180)
    assert q.returncode==0,(q.stdout,q.stderr)
    assert (d/'equation10-22.tex').read_bytes()==tex.read_bytes()
    assert (d/'equation10-22.pdf').read_bytes()==pdf.read_bytes()
    builds=[]
    for name in ('a','b'):
        out=root/name;out.mkdir()
        p=subprocess.run(['pdflatex','-halt-on-error','-interaction=batchmode','-output-directory',str(out),'equation10-22.tex'],cwd=d,text=True,capture_output=True,timeout=180)
        assert p.returncode==0,(p.stdout,p.stderr)
        log=(out/'equation10-22.log').read_text(errors='replace')
        assert not re.search(r'overfull|underfull|warning',log,re.I)
        builds.append(H(out/'equation10-22.pdf'))
    assert builds == [H(pdf),H(pdf)]
info=subprocess.run(['pdfinfo',str(pdf)],text=True,capture_output=True,check=True).stdout
assert re.search(r'^Pages:\s+2\s*$',info,re.M)
for page in (1,2):
    extracted=subprocess.run(['pdftotext','-layout','-f',str(page),'-l',str(page),str(pdf),'-'],text=True,capture_output=True,check=True).stdout
    assert len(extracted)>500
    assert ('twenty-two-variable' in extracted if page==1 else '114-operation circuit' in extracted)
assert {str(x.resolve()): H(x) for x in inputs} == before
result={'status':'PASS_INDEPENDENT_AQ22_DISPLAY','inputs_sha256':before,
        'unknowns':22,'fixed_ports':4,'printed_gates':114,'output_squares':13,
        'finite_degree':10,'positive_reconstruction':'retained g72 forces QComputed=(n*g)^2 at a zero',
        'mutations':['gate_operation','gate_operand','gate_target','decimal_digit','unknown_duplicate'],
        'pdf_pages':2,'pdf_sha256':H(pdf),'independent_build_sha256':builds,
        'scope':'Finite display/graph binding and ordinary positivity reasoning. No Lean transport, iPRA derivation, formal TeX decoder/rank semantics, or minimality claim.'}
out=HERE/'receipt.json'
assert not out.exists()
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(result['status'], H(out), H(pdf))
