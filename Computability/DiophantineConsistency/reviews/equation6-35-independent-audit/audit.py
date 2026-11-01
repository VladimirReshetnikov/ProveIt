#!/usr/bin/env python3
"""Independent gate-chain, document generation and PDF audit; no source edits."""
from pathlib import Path
import hashlib,json,re,runpy,shutil,subprocess,tempfile,contextlib,io
D=Path(__file__).resolve().parent;ROOT=D.parents[1];R=ROOT/'research/adaptive-square-sums35';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
lean=ROOT/'Lean/DiophantineConsistency/AdaptiveAQ35Literal.lean';tex=ROOT/'equation6-35.tex';pdf=ROOT/'equation6-35.pdf';cand=R/'candidate.json';fragment=R/'equation6-35-display.tex';gen=R/'generate_equation6_35.py';gen_candidate=R/'generate.py';fixed=ROOT/'equation.tex';parent=R.parent/'adaptive-square-sums36/candidate.json';validator=R/'verify_display6_35.py';degree=R/'verify_degree.py';substitution=R/'verify_substitution.py';prior=R.parent/'adaptive-direct-ordinate86/verify_display_tex86.py';olddegree=R.parent/'adaptive-square-sums36/verify_degree.py'
inputs=[Path(__file__).resolve(),lean,tex,pdf,cand,fragment,gen,gen_candidate,fixed,parent,validator,degree,substitution,prior,olddegree];before={str(p.resolve()):H(p) for p in inputs};c=json.loads(cand.read_text());assert len(c['witnesses'])==35 and len(set(c['witnesses']))==35 and c['operations']==len(c['source'])==145
text=lean.read_text();variables=re.findall(r'^  let (\w+) : Expr \(Fin 35\) := \.var (\d+)$',text,re.M);assert variables==[(n,str(i)) for i,n in enumerate(c['witnesses'])];ports=re.findall(r'^  let (\w+) : Expr \(Fin 35\) := \.constant \(p (\d+)\)$',text,re.M);assert ports==[(n,str(i)) for i,n in enumerate(c['fixed_numerals'])]
lets=re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',text,re.M);assert len(lets)==145
for number,((name,op,a,b),(ln,la,lo,lb)) in enumerate(zip(c['source'],lets),1):assert (name,str(a),op,str(b))==(ln,la,lo,lb),('Lean/candidate gate',number)
assert re.search(r'^  '+re.escape(c['output'])+r'\s*$',text,re.M)
# Independently infer every printed gate alias while binding all inputs by hand.
ren={'i':'g','r':'xi','y':'upsilon','squareVariable':'vartheta','scaleVariable':'psi','mainScaleVariable':'varphi','rankVariable':'epsilon','cVariable':'cNamed','ellVariable':'ellNamed','wPositive':'h','wNegative':'t','fSquareVariable':'m','cSquareVariable':'n','zPositive':'p','zNegative':'j','dPositive':'d','dNegative':'o','vPositive':'e','vNegative':'z','deltaVariable':'delta','qSquareVariable':'kappa','productVariable2':'lambda','ellProductVariable':'tau','varphiSquareVariable':'chi','scaledIndexVariable':'theta','qValueVariable':'Q','K0':'K','MC':'mu','MF':'omega'}
def word(x):return str(x).replace(r'\_','_')
def check_printed(body_text):
    alias={n:ren.get(n,n) for n in c['witnesses']+c['fixed_numerals']};assert len(set(alias.values()))==39
    lines=[x for x in body_text.splitlines() if re.match(r'^\d+\. ',x)];assert len(lines)==145
    seen=set(alias.values())
    for number,(row,line) in enumerate(zip(c['source'],lines),1):
     match=re.fullmatch(r'(\d+)\. (\S+) = (\S+) ([+*\-]) (\S+)\\\\',line);assert match and int(match[1])==number,('printed gate syntax',number)
     n,op,a,b=row;shown=word(match[2]);assert shown not in seen and op==match[4] and word(match[3])==(alias[a] if isinstance(a,str) else str(a)) and word(match[5])==(alias[b] if isinstance(b,str) else str(b)),('candidate/printed gate',number);alias[n]=shown;seen.add(shown)
    assert c['output'] in alias and alias[c['output']]==word(re.fullmatch(r'148\. (\S+) = .*',lines[-1])[1])
    return lines
lines=check_printed(tex.read_text())
# Existing independent sparse-polynomial validator checks each of the 44
# displayed definitions and all 22 residual squares. Exercise new controls.
with contextlib.redirect_stdout(io.StringIO()) as capture:v=runpy.run_path(str(validator))
assert v['count']==44;raw=tex.read_text();tests=[('display_sign',r'\epsilon-R',r'\epsilon+R'),('gate_operand','145. add\\_qSigned = add\\_scaledIndex + qSignedConstraint', '145. add\\_qSigned = add\\_scaledIndex - qSignedConstraint'),('extra_square',r'\mathcal{P}^2+',r'\mathcal{P}^2+1+'),('unknown',r'\kappa,\lambda,\tau,\chi,\theta,Q\in',r'\kappa,\lambda,\tau,\chi,\theta,Z\in')]
# The validator's validate() checks the display block; gate mutation is tested
# separately against the independently inferred mapping above.
for label,old,new in tests:
 assert old in raw,label
 if label=='gate_operand':
  changed=raw.replace(old,new,1)
  try:check_printed(changed)
  except AssertionError:pass
  else:raise AssertionError('undetected printed-gate mutation')
 else:
  try:v['validate'](raw.replace(old,new,1))
  except ValueError:pass
  else:raise AssertionError(('undetected display mutation',label))
# Regenerate candidate and presentation in a separate directory, never editing
# the supplied files. The fixed constants are copied from the pinned original.
with tempfile.TemporaryDirectory(prefix='eq35-independent-') as td:
 root=Path(td);dr=root/'research/adaptive-square-sums35';dr.mkdir(parents=True);dp=root/'research/adaptive-square-sums36';dp.mkdir();shutil.copyfile(parent,dp/'candidate.json');shutil.copyfile(gen_candidate,dr/'generate.py');shutil.copyfile(gen,dr/'generate_equation6_35.py');shutil.copyfile(fragment,dr/'equation6-35-display.tex');shutil.copyfile(fixed,root/'equation.tex');
 for command in ([str(dr/'generate.py')],[str(dr/'generate_equation6_35.py')]):
  p=subprocess.run(['python3',*command],cwd=root,capture_output=True,text=True);assert p.returncode==0,(command,p.stdout,p.stderr)
 assert (dr/'candidate.json').read_bytes()==cand.read_bytes() and (root/'equation6-35.tex').read_bytes()==tex.read_bytes()
 pdfhash=[]
 for i in range(2):
  out=root/('build'+str(i));out.mkdir();p=subprocess.run(['pdflatex','-halt-on-error','-interaction=batchmode','-output-directory',str(out),str(root/'equation6-35.tex')],cwd=root,capture_output=True,text=True);assert p.returncode==0,(p.stdout,p.stderr);pdfhash.append(H(out/'equation6-35.pdf'))
 assert pdfhash==[H(pdf),H(pdf)],('PDF mismatch',pdfhash,H(pdf))
info=subprocess.run(['pdfinfo',str(pdf)],capture_output=True,text=True,check=True).stdout;assert re.search(r'^Pages:\s+2\s*$',info,re.M)
for page in (1,2):
 p=subprocess.run(['pdftotext','-layout','-f',str(page),'-l',str(page),str(pdf),'-'],capture_output=True,text=True,check=True);assert len(p.stdout)>500
 if page==1:assert 'thirty-five' in p.stdout and 'fixed integers' in p.stdout
 else:assert '145-operation circuit' in p.stdout and '145.' in p.stdout
assert {str(p.resolve()):H(p) for p in inputs}==before
out={'status':'PASS_INDEPENDENT_DISPLAY_AUDIT','inputs_sha256':before,'lean_candidate_printed_gate_count':148,'literal_variables':35,'fixed_ports':4,'display_definitions':44,'residual_squares':22,'additional_mutation_controls':[x[0] for x in tests],'pdf_pages':2,'pdf_sha256':H(pdf),'clean_pdf_build_sha256':pdfhash,'scope':'Display, finite arithmetic checks, gate identity and PDF reproducibility; native proof provenance is separately qualified.'};p=D/'receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],145,44,22,H(p))
