#!/usr/bin/env python3
"""Fresh scoped BCH review: only inert Git/text/CSV inputs, exact path matrices."""
import csv,hashlib,io,itertools,json,math,re,subprocess
from fractions import Fraction as F
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
BASE='Algebra/BakerCampbellHausdorff/'
TEX=BASE+'docs/combined/tex/'
REV='ad52ef11e'
def need(x,s):
 if not x:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(p):return subprocess.check_output(['git','show',REV+':'+p],cwd=ROOT)
def zero(n):return [[F(0) for _ in range(n)] for _ in range(n)]
def ident(n):
 a=zero(n)
 for i in range(n):a[i][i]=F(1)
 return a
def mm(a,b):
 n=len(a); c=zero(n)
 for i in range(n):
  for k in range(i,n):
   if a[i][k]:
    for j in range(k,n):c[i][j]+=a[i][k]*b[k][j]
 return c
def plus(a,b,scale=F(1)):return [[x+scale*y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def exponential(a):
 n=len(a); out=ident(n);power=ident(n)
 for k in range(1,n):
  power=mm(power,a);out=plus(out,power,F(1,math.factorial(k)))
 return out
def coefficient(w):
 n=len(w)+1;x=zero(n);y=zero(n)
 for i,c in enumerate(w):(x if c=='X' else y)[i][i+1]=F(1)
 u=plus(mm(exponential(x),exponential(y)),ident(n),-1)
 power=ident(n); out=F(0)
 for k in range(1,n):
  power=mm(power,u);out+=F((-1)**(k-1),k)*power[0][-1]
 return out

def build():
 ranges=[(BASE+'README.md',1,25),(TEX+'01_scope.tex',1,205),(TEX+'02_formal.tex',1,249),(TEX+'03_hopf.tex',249,294),(TEX+'14_computation.tex',1,143),(TEX+'07_convergence.tex',28,65),(TEX+'07_convergence.tex',208,245),(TEX+'appendix_lean.tex',369,376)]
 spans=[]
 for p,a,b in ranges:
  raw=blob(p);lines=raw.splitlines(keepends=True);need(b<=len(lines),'span range')
  part=b''.join(lines[a-1:b]);spans.append({'commit':REV,'path':p,'first':a,'last':b,'blob_sha256':sha(raw),'span_sha256':sha(part)})
 csvpath=BASE+'docs/combined/data/bch_associative.csv';raw=blob(csvpath);rows=list(csv.DictReader(io.StringIO(raw.decode())));table={}
 for row in rows:
  w=row['word'];degree=int(row['degree']);a=int(row['numerator']);b=int(row['denominator'])
  need(w not in table and set(w)<=set('XY') and len(w)==degree and 1<=degree<=12 and a and b>0,'CSV schema')
  need(math.gcd(a,b)==1,'reduced fraction');table[w]=F(a,b)
  scale=math.factorial(degree)*math.lcm(*range(1,degree+1));need(scale%b==0,'integer denominator scale')
 results=[]
 for n in range(1,7):
  for tup in itertools.product('XY',repeat=n):
   w=''.join(tup);actual=coefficient(w);need(actual==table.get(w,F(0)),'path matrix coefficient '+w)
   results.append([w,actual.numerator,actual.denominator])
 old=blob(TEX+'02_formal.tex');current=(ROOT/TEX/'02_formal.tex').read_bytes();oldlabels=set(re.findall(rb'\\label\{([^}]+)\}',old));newlabels=set(re.findall(rb'\\label\{([^}]+)\}',current))
 need(oldlabels<=newlabels and newlabels-oldlabels=={b'rem:analytic-inverse-domain'},'label retention')
 need(b'2\\pi\\ii' in current and b'\\norm A<\\log2' in current,'domain correction present')
 diffs=[]
 for p in [BASE+'.gitignore',BASE+'README.md',BASE+'Lean/README.md',TEX+'appendix_lean.tex','README.md','lakefile.toml']:
  rawdiff=subprocess.check_output(['git','diff','abb123637',REV,'--',p],cwd=ROOT)
  diffs.append({'path':p,'sha256':sha(rawdiff),'lines':len(rawdiff.splitlines())})
 return {'schema':'scoped BCH formal interface review v1','helper_sha256':sha(Path(__file__).read_bytes()),'read_spans':spans,'read_lines':sum(s['last']-s['first']+1 for s in spans),'adaptation_text_diffs':diffs,'csv':{'path':csvpath,'sha256':sha(raw),'rows':len(rows),'denominator_checks':len(rows)},'path_matrix_checks':len(results),'coefficient_results':results,'corrected_source':{'path':TEX+'02_formal.tex','sha256':sha(current),'retained_labels':len(oldlabels),'new_label':'rem:analytic-inverse-domain'},'scope':{'old_helpers_executed':False,'Lean_build_or_axiom_check':False,'all_orders_Lie_proof_certified':False,'analytic_convergence_proof_certified':False,'source_archives_audited':False,'full_degree12_coefficients_recomputed':False,'universal_bound_changed':False}}
if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--expect',type=Path);a=p.parse_args();out=(json.dumps(build(),indent=2,sort_keys=True)+'\n').encode()
 if a.expect:need(a.expect.read_bytes()==out,'exact receipt equality')
 else:Path('/tmp/review_bch_ad52ef11e.json').write_bytes(out)
 print('PASS: 126 word-selecting path matrices, all supplied denominator scales, scoped immutable inputs')
