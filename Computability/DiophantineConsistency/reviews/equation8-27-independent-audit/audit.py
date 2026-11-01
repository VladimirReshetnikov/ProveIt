#!/usr/bin/env python3
"""Independent provisional circuit and document audit; no edits to inputs."""
import contextlib,hashlib,io,json,re,runpy,shutil,subprocess,tempfile
from pathlib import Path
D=Path(__file__).resolve().parent; ROOT=D.parents[1]; R=ROOT/'research/adaptive-square-sums27-degree8'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
cand=R/'candidate.json'; tex=ROOT/'equation8-27.tex'; pdf=ROOT/'equation8-27.pdf'; validator=R/'verify_display8_27.py'
inputs=[cand,tex,pdf,validator,R/'generate.py',R/'generate_equation8_27.py',R/'equation8-27-display.tex',ROOT/'equation.tex',R.parent/'adaptive-square-sums28-degree8/candidate.json']
before={str(p.relative_to(ROOT)):H(p) for p in inputs}; c=json.loads(cand.read_text()); assert len(c['witnesses'])==len(set(c['witnesses']))==27 and len(c['source'])==c['operations']==129
known=set(c['witnesses']+c['fixed_numerals']); assert len(known)==31
rows={}
for name,op,a,b in c['source']:
 assert name not in known and op in ('+','-','*') and all(isinstance(v,int) or v in known for v in (a,b)); known.add(name); rows[name]=(op,a,b)
live={c['output']};todo=list(live)
while todo:
 for v in rows.get(todo.pop(),('',))[1:]:
  if isinstance(v,str) and v not in live:live.add(v);todo.append(v)
assert set(rows)<=live and set(c['witnesses']+c['fixed_numerals'])<=live
ren={'i':'g','r':'xi','y':'upsilon','scaleVariable':'psi','mainScaleVariable':'varphi','rankVariable':'epsilon','cVariable':'cNamed','ellVariable':'ellNamed','cSquareVariable':'n','zValueVariable':'Z','dValueVariable':'D','vValueVariable':'V','deltaVariable':'delta','qSquareVariable':'kappa','productVariable2':'lambda','scaledIndexVariable':'theta','qValueVariable':'Q','K0':'K','MC':'mu','MF':'omega'}
def word(x):return str(x).replace(r'\_','_')
def check_gates(text):
 alias={n:ren.get(n,n) for n in c['witnesses']+c['fixed_numerals']};assert len(set(alias.values()))==31;seen=set(alias.values()); lines=[x for x in text.splitlines() if re.match(r'^\d+\. ',x)];assert len(lines)==129
 for i,((name,op,a,b),line) in enumerate(zip(c['source'],lines),1):
  m=re.fullmatch(r'(\d+)\. (\S+) = (\S+) ([+*\-]) (\S+)\\\\',line);assert m and int(m[1])==i
  shown=word(m[2]);assert shown not in seen and m[4]==op and word(m[3])==(alias[a] if isinstance(a,str) else str(a)) and word(m[5])==(alias[b] if isinstance(b,str) else str(b));alias[name]=shown;seen.add(shown)
 assert alias['f2']=='m' and alias['g40']=='g40' and alias['g62']=='g62' and alias[c['output']]==word(re.match(r'129\. (\S+)',lines[-1])[1]);return alias
raw=tex.read_text();a=check_gates(raw)
assert r'gate \texttt{m} is $m=f^2$' in raw and r'gates \texttt{g40, g62} compute $\tau,\chi$' in raw
assert all(fragment in raw for fragment in (
 r'\texttt{cNamed, ellNamed} are $c,\ell$',
 r'gate \texttt{a} is the displayed abbreviation',
 r'gate \texttt{WComputed} is the displayed abbreviation $W=C(X+Kq)-Fq$',
 r'\texttt{n, Z, D, V, delta} are the displayed',
 r'\texttt{kappa, lambda, theta, Q}',
 r'\texttt{q3, g55, g39, y2, g80} compute $s,x,\sigma,\nu,\vartheta$',
 r'Gates \texttt{E, I} compute', r'$XY,ng$', r'$E=\lambda$, $I=\theta$'))
for row in ('4. q3 = q * kappa', '8. E = X * Y', '13. a = lambda + Y',
            '26. WComputed = g27 - g28', '37. g39 = psi * psi',
            '38. g40 = ellNamed * g30', '53. g55 = lambda * q',
            '60. g62 = varphi * varphi', '65. m = f * f', '68. I = n * g',
            '75. y2 = upsilon * upsilon', '76. g80 = V * V'):
 assert row+r'\\' in raw,('explanatory gate alias',row)
assert 'its model witness transport and native intuitionistic PRA equivalence have not yet been proved in Lean' in raw
with contextlib.redirect_stdout(io.StringIO()):v=runpy.run_path(str(validator))
assert v['count']==40
for label,old,new in [('sign',r'\epsilon-R',r'\epsilon+R'),('extra_square',r'\mathcal{P}^2+',r'\mathcal{P}^2+1+'),('unknown',r'\kappa,\lambda,\theta,Q\in',r'\kappa,\lambda,\theta,Z\in')]:
 assert old in raw,label
 try:v['validate'](raw.replace(old,new,1))
 except ValueError:pass
 else:raise AssertionError(('undetected',label))
old='129. add\\_qSigned = add\\_scaledIndex + qSignedConstraint';assert old in raw
try:check_gates(raw.replace(old,old.replace(' + ',' - '),1))
except AssertionError:pass
else:raise AssertionError('undetected gate mutation')
with tempfile.TemporaryDirectory(prefix='eq27-audit-') as td:
 root=Path(td);dr=root/'research/adaptive-square-sums27-degree8';dr.mkdir(parents=True);dp=root/'research/adaptive-square-sums28-degree8';dp.mkdir();shutil.copyfile(inputs[-1],dp/'candidate.json')
 for f in ('generate.py','generate_equation8_27.py','equation8-27-display.tex'):shutil.copyfile(R/f,dr/f)
 shutil.copyfile(ROOT/'equation.tex',root/'equation.tex')
 for f in ('generate.py','generate_equation8_27.py'):
  p=subprocess.run(['python3',str(dr/f)],cwd=root,text=True,capture_output=True);assert p.returncode==0,(p.stdout,p.stderr)
 assert H(dr/'candidate.json')==H(cand) and H(root/'equation8-27.tex')==H(tex)
 hashes=[]
 for i in range(2):
  out=root/f'build{i}';out.mkdir();p=subprocess.run(['pdflatex','-halt-on-error','-interaction=batchmode','-output-directory',str(out),str(root/'equation8-27.tex')],cwd=root,capture_output=True,text=True);assert p.returncode==0,(p.stdout,p.stderr)
  log=(out/'equation8-27.log').read_text();assert not re.search(r'Overfull|Underfull|Font Warning',log); hashes.append(H(out/'equation8-27.pdf'))
 assert hashes==[H(pdf),H(pdf)]
info=subprocess.run(['pdfinfo',str(pdf)],text=True,capture_output=True,check=True).stdout;assert re.search(r'^Pages:\s+2\s*$',info,re.M)
for page in (1,2):
 txt=subprocess.run(['pdftotext','-layout','-f',str(page),'-l',str(page),str(pdf),'-'],text=True,capture_output=True,check=True).stdout;assert len(txt)>500 and ('twenty-seven' if page==1 else '129-operation circuit') in txt
assert before=={str(p.relative_to(ROOT)):H(p) for p in inputs}
receipt={'status':'PASS_INDEPENDENT_PROVISIONAL_DISPLAY','inputs_sha256':before,'variables':27,'ports':4,'gates':129,'definitions':40,'squares':18,'mutation_controls':['sign','extra_square','unknown','gate_operator'],'pdf_sha256':H(pdf),'clean_builds':hashes,'scope':'Finite graph and provisional display only; no Lean model or native theorem is asserted.'}
(D/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n'); print(receipt['status'],receipt['pdf_sha256'])
