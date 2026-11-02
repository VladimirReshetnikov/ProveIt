#!/usr/bin/env python3
"""Independently audit the staged 26-variable display and circuit."""
import contextlib, hashlib, io, json, re, runpy, shutil, subprocess, tempfile
from pathlib import Path
if not __debug__:
    raise RuntimeError('this audit requires Python assertions enabled')
D=Path(__file__).resolve().parent; ROOT=D.parents[1]; R=ROOT/'research/adaptive-square-sums26-degree8'
H=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
cand=R/'candidate.json';tex=R/'equation8-26.tex';pdf=R/'equation8-26.pdf';validator=R/'verify_display8_26.py'
literal=ROOT/'reviews/ipra-standard-aq26-combined-author-trial/src/DiophantineConsistency/AdaptiveAQ26Literal.lean'
state=ROOT/'reviews/ipra-standard-aq26-combined-author-trial/state.json'
inputs=[Path(__file__).resolve(),cand,tex,pdf,validator,R/'generate.py',R/'generate_equation8_26.py',R/'equation8-26-display.tex',R/'verify_degree.py',R/'verify_substitution.py',ROOT/'equation.tex',R.parent/'adaptive-square-sums27-degree8/candidate.json',literal,state]
before={str(p.resolve()):H(p) for p in inputs};c=json.loads(cand.read_text());assert H(cand)=='d8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5'
assert len(c['witnesses'])==len(set(c['witnesses']))==26 and len(c['source'])==c['operations']==126
known=set(c['witnesses']+c['fixed_numerals']);assert len(known)==30;rows={}
for name,op,a,b in c['source']:
 assert name not in known and op in ('+','-','*') and all(isinstance(v,int) or v in known for v in (a,b));known.add(name);rows[name]=(op,a,b)
live={c['output']};todo=list(live)
while todo:
 for v in rows.get(todo.pop(),('',))[1:]:
  if isinstance(v,str) and v not in live:live.add(v);todo.append(v)
assert set(rows)<=live and set(c['witnesses']+c['fixed_numerals'])<=live
# Read the historical Lean literal without using its author-side checker.
source=literal.read_text();start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 26) :=\n');end=source.index('\nend DiophantineConsistency.AdaptiveAQ26Literal',start)
want=['def literal (p : Fin 4 → ℤ) : Expr (Fin 26) :=']+[f'  let {n} : Expr (Fin 26) := .var {i}' for i,n in enumerate(c['witnesses'])]+[f'  let {n} : Expr (Fin 26) := .constant (p {i})' for i,n in enumerate(c['fixed_numerals'])]+[f'  let {n} := {a} {op} {b}' for n,op,a,b in c['source']]+['  '+c['output']]
assert source[start:end].splitlines()==want
s=json.loads(state.read_text());assert s['status']=='AUTHOR_ONLY_PASS';r=next(x for x in s['rows'] if x['module']=='DiophantineConsistency.AdaptiveAQ26Literal');assert r['exit']==0 and r['source_sha256']==H(literal)
# Independent one-to-one gate renaming: bind just input names and infer all gates.
ren={'i':'g','r':'xi','y':'upsilon','scaleVariable':'psi','mainScaleVariable':'varphi','rankVariable':'epsilon','cVariable':'cNamed','ellVariable':'ellNamed','cSquareVariable':'n','zValueVariable':'Z','dValueVariable':'D','vValueVariable':'V','deltaVariable':'delta','qSquareVariable':'kappa','productVariable2':'lambda','qValueVariable':'Q','K0':'K','MC':'mu','MF':'omega'}
def word(x):return str(x).replace(r'\_','_')
def check_gates(t):
 alias={n:ren.get(n,n) for n in c['witnesses']+c['fixed_numerals']};assert len(set(alias.values()))==30;seen=set(alias.values());lines=[x for x in t.splitlines() if re.match(r'^\d+\. ',x)];assert len(lines)==126
 for i,((name,op,a,b),line) in enumerate(zip(c['source'],lines),1):
  m=re.fullmatch(r'(\d+)\. (\S+) = (\S+) ([+*\-]) (\S+)\\\\',line);assert m and int(m[1])==i
  shown=word(m[2]);assert shown not in seen and m[4]==op and word(m[3])==(alias[a] if isinstance(a,str) else str(a)) and word(m[5])==(alias[b] if isinstance(b,str) else str(b));alias[name]=shown;seen.add(shown)
 assert alias['f2']=='m' and alias['g40']=='g40' and alias['g62']=='g62' and alias[c['output']]==word(re.match(r'126\. (\S+)',lines[-1])[1]);return alias
raw=tex.read_text();alias=check_gates(raw)
assert 'model transport and native intuitionistic PRA equivalence have passed one historical author run, but not a paired replay' in raw
assert 'single-overlay standard-theory AQ26 client has also passed one author run' in raw
for f in (r'\texttt{cNamed, ellNamed} are $c,\ell$',r'gate \texttt{a} is the displayed abbreviation',r'gate \texttt{WComputed} is the displayed abbreviation $W=C(X+Kq)-Fq$',r'gate \texttt{m} is $m=f^2$',r'\texttt{n, Z, D, V, delta} are the displayed',r'\texttt{kappa, lambda, Q}',r'\texttt{q3, g55, g39, y2, g80} compute $s,x,\sigma,\nu,\vartheta$',r'gates \texttt{g40, g62} compute $\tau,\chi$',r'Gates \texttt{E, I} compute',r'$XY,ng$',r'$E=\lambda$, $I=ng$'):assert f in raw,f
for row in ('4. q3 = q * kappa','8. E = X * Y','13. a = lambda + Y','26. WComputed = g27 - g28','37. g39 = psi * psi','38. g40 = ellNamed * g30','53. g55 = lambda * q','60. g62 = varphi * varphi','65. m = f * f','68. I = n * g','75. y2 = upsilon * upsilon','76. g80 = V * V'):assert row+r'\\' in raw,row
original=(ROOT/'equation.tex').read_text();lo=original.index(r'\textbf{The four fixed integers.}');hi=original.index(r'\endgroup',original.index(r'\textbf{The integer $\mathcal A$'))+len(r'\endgroup');block=original[lo:hi];assert block in raw and H(ROOT/'equation.tex')==before[str((ROOT/'equation.tex').resolve())];assert 'base 10' in block and re.search(r'\d{60,}\\par',block)
with contextlib.redirect_stdout(io.StringIO()):v=runpy.run_path(str(validator))
assert v['count']==39
for label,old,new in [('sign',r'\epsilon-R',r'\epsilon+R'),('extra_square',r'\mathcal{P}^2+',r'\mathcal{P}^2+1+'),('unknown',r'\kappa,\lambda,Q\in',r'\kappa,\lambda,Z\in')]:
 assert old in raw,label
 try:v['validate'](raw.replace(old,new,1))
 except ValueError:pass
 else:raise AssertionError(('undetected mutation',label))
old=r'126. add\_qSigned = add\_product2 + qSignedConstraint';assert old in raw
try:check_gates(raw.replace(old,old.replace(' + ',' - '),1))
except AssertionError:pass
else:raise AssertionError('undetected printed-gate mutation')
with tempfile.TemporaryDirectory(prefix='eq26-independent-') as td:
 root=Path(td);dr=root/'research/adaptive-square-sums26-degree8';dr.mkdir(parents=True);dp=root/'research/adaptive-square-sums27-degree8';dp.mkdir();shutil.copyfile(inputs[-3],dp/'candidate.json')
 for f in ('generate.py','generate_equation8_26.py','equation8-26-display.tex'):shutil.copyfile(R/f,dr/f)
 shutil.copyfile(ROOT/'equation.tex',root/'equation.tex')
 for f in ('generate.py','generate_equation8_26.py'):
  p=subprocess.run(['python3',str(dr/f)],cwd=root,text=True,capture_output=True);assert p.returncode==0,(p.stdout,p.stderr)
 assert H(dr/'candidate.json')==H(cand) and H(dr/'equation8-26.tex')==H(tex)
 hashes=[]
 for i in range(2):
  out=root/f'build{i}';out.mkdir();p=subprocess.run(['pdflatex','-halt-on-error','-interaction=batchmode','-output-directory',str(out),'equation8-26.tex'],cwd=dr,capture_output=True,text=True);assert p.returncode==0,(p.stdout,p.stderr)
  log=(out/'equation8-26.log').read_text();assert not re.search(r'overfull|underfull|warning',log,re.I);hashes.append(H(out/'equation8-26.pdf'))
 assert hashes==[H(pdf),H(pdf)]
info=subprocess.run(['pdfinfo',str(pdf)],text=True,capture_output=True,check=True).stdout;assert re.search(r'^Pages:\s+2\s*$',info,re.M)
for page in (1,2):
 txt=subprocess.run(['pdftotext','-layout','-f',str(page),'-l',str(page),str(pdf),'-'],text=True,capture_output=True,check=True).stdout;assert len(txt)>500 and ('twenty-six' if page==1 else '126-operation circuit') in txt
assert before=={str(p.resolve()):H(p) for p in inputs}
receipt={'status':'PASS_INDEPENDENT_STAGED_DISPLAY','inputs_sha256':before,'variables':26,'ports':4,'gates':126,'definitions':39,'squares':17,'mutation_controls':['sign','extra_square','unknown','gate_operator'],'pdf_sha256':H(pdf),'clean_builds':hashes,'scope':'Finite display, circuit and historical literal source binding; not another Lean replay, a paired/current-source proof, or a Lean degree theorem. The fixed constant block is byte-identical to equation.tex; its semantic recipe has a separately documented manual-transcription boundary.'}
target=D/'receipt.json';assert not target.exists();target.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(receipt['status'],H(target),H(pdf))
