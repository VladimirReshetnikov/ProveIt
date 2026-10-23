from pathlib import Path
import ast,json,hashlib,tempfile,shutil,subprocess,os
import sympy as s
R=Path(__file__).resolve().parents[2];P=R/'quartic';O=Path(__file__).resolve().parent
snap={str(p.relative_to(P)):hashlib.sha256(p.read_bytes()).hexdigest()for p in P.rglob('*')if p.is_file() and '__pycache__'not in p.parts};(O/'SNAPSHOT.json').write_text(json.dumps(snap,indent=2)+'\n')
def req(t,m):
 if not t:raise ValueError(m)
old=json.loads((P/'upstream/q45/quartic45.json').read_text());new=json.loads((P/'quartic42.json').read_text())
removed={f'{a}_pos{i}'for a in ['eta','zeta']for i in [1,2,3]};added=['pair_pos1','pair_pos2','pair_pos3'];variables=[v for v in old['variables'] if v not in removed]+added
req(new['variables']==variables,'precise variable change');req(len(variables)==42,'variable count')
expected=old['residuals'][:23]+old['residuals'][25:];req(expected[22]=='-u**2 + w','scale old');expected[22]='-4*u**2 + w';expected+=['eta*zeta-pair_pos1**2-pair_pos2**2-pair_pos3*(pair_pos3+1)-1'];req(new['residuals']==expected,'exact residual change');req(len(expected)==27,'residual count')
fixed=old['fixed_numerals'];names=variables+fixed;symbols={a:s.Symbol(a)for a in names}
def parse(x):
 if isinstance(x,ast.Expression):return parse(x.body)
 if isinstance(x,ast.Constant) and type(x.value)is int:return s.Integer(x.value)
 if isinstance(x,ast.Name) and x.id in symbols:return symbols[x.id]
 if isinstance(x,ast.UnaryOp) and isinstance(x.op,ast.USub):return -parse(x.operand)
 if isinstance(x,ast.BinOp):
  a,b=parse(x.left),parse(x.right)
  if isinstance(x.op,ast.Add):return a+b
  if isinstance(x.op,ast.Sub):return a-b
  if isinstance(x.op,ast.Mult):return a*b
  if isinstance(x.op,ast.Pow) and b.is_Integer and 0<=b<=4:return a**b
 raise ValueError('unsafe syntax')
polys=[parse(ast.parse(t,mode='eval'))for t in expected];vs=[symbols[v]for v in variables];allsy=[symbols[v]for v in names]
req(all(s.Poly(p,*vs).total_degree()==2 for p in polys),'quadratic');Q=s.Poly(sum(p*p for p in polys),*allsy);terms=dict(Q.terms());exp=json.loads((P/'quartic42_expanded.json').read_text());req(exp['variables']==names,'expanded variable order');req(terms=={tuple(t['exponents']):t['coefficient']for t in exp['terms']},'independent expansion');tau=[0]*len(names);tau[names.index('tau')]=4;req(terms.get(tuple(tau))==1,'tau4');req(max(sum(e[:42])for e in terms)==4,'quartic');req(set.union(*(p.free_symbols for p in polys))==set(allsy),'liveness')
base=R/'sources/ConZFC_Separated_Degrees_2026-10-23/con-zfc-separated-degrees-2026-10-23/quartic';pins=json.loads((P/'SOURCE_PINS.json').read_text())['files'];n=0
for path,h in pins.items():
 q=P/path;req(hashlib.sha256(q.read_bytes()).hexdigest()==h,'pinned hash '+path)
 if base.exists() and path.startswith('upstream/q45/'):
  oldp=base/path[len('upstream/q45/'):];req(oldp.read_bytes()==q.read_bytes(),'original tree equality '+path);n+=1
runs=[]
with tempfile.TemporaryDirectory()as t:
 w=Path(t)/'quartic';shutil.copytree(P,w,ignore=shutil.ignore_patterns('__pycache__'))
 for flag in [[],['-O']]:
  p=subprocess.run(['python','-B']+flag+['build_verify.py'],cwd=w,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),capture_output=True,text=True);req(p.returncode==0,'replay '+p.stderr);tag='optimized'if flag else'normal';(O/(tag+'.stdout.txt')).write_text(p.stdout);runs.append({'mode':tag,'returncode':p.returncode})
  for artifact in ['quartic42.json','quartic42_expanded.json']:req((w/artifact).read_bytes()==(P/artifact).read_bytes(),'byte-identical rebuild '+artifact)
result={'status':'PASS','variables':42,'residuals':27,'degree':4,'terms':len(terms),'tau4':1,'original_input_files_byte_identical':n,'original_tree_comparison_performed':base.exists(),'retained_source_hashes_checked':len(pins),'exactly_intended_changes':True,'independent_sympy_expansion':True,'runs':runs,'source_and_expansion_sha256':{a:snap[a]for a in ['quartic42.json','quartic42_expanded.json','PROOF.md','build_verify.py']}};(O/'LITERAL_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
