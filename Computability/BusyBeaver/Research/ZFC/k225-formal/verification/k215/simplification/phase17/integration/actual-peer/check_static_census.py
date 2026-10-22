"""Run only extracted owned static literal-census statements; no actual audit/build."""
from pathlib import Path
from collections import Counter
import ast,hashlib,json,re
D=Path(__file__).resolve().parent;P=Path('/tmp/k215-phase17-actual-review/review_actual.py');data=P.read_bytes();pin=hashlib.sha256(data).hexdigest();assert pin=='b91ce61fd2cc2c24ad30fbcb4bf4fb50889bb02e11ad0493085581a703bb755e'
t=ast.parse(data);main=next(n for n in t.body if isinstance(n,ast.FunctionDef)and n.name=='main')
# Only finite literal-census region, beginning at program text assignment and ending
# before endpoint import-closure calculation. This executes no actual evidence audit.
def assigns(n,name):return isinstance(n,ast.Assign)and any(isinstance(x,ast.Name)and x.id==name for x in n.targets)
lo=next(i for i,n in enumerate(main.body)if assigns(n,'program'))
hi=next(i for i,n in enumerate(main.body)if assigns(n,'endpoint'))
statements=main.body[lo:hi];assert any(isinstance(n,ast.FunctionDef)and n.name=='walk'for n in statements)
assert not any(isinstance(n,(ast.Import,ast.ImportFrom))for n in ast.walk(ast.Module(body=statements,type_ignores=[])))
plan=json.loads(Path('/tmp/k215-phase17-check/plan.json').read_text());selected={r['module']:r for r in plan['modules']};oldrows={}
for name in ['primary-run1','compatibility-run1']:
 inv=json.loads((Path('/tmp/k215-phase16-check')/name/'inventory.json').read_text());oldrows.update({r['module']:r for r in inv['modules']})
space={'Path':Path,'Counter':Counter,'json':json,'re':re,'R':Path('/home/codex/.codex/worktrees/ec20/Proofs'),'selected':selected,'oldrows':oldrows,'fresh':plan['expected']['fresh_by_source_transitivity'],'read':lambda p:json.loads(Path(p).read_text())}
code=ast.fix_missing_locations(ast.Module(body=statements,type_ignores=[]));exec(compile(code,str(P)+' [only static literal census]','exec'),space)
assert hashlib.sha256(P.read_bytes()).hexdigest()==pin
result={'status':'PASS_EXTRACTED_OWNED_STATIC_CENSUS','helper_sha256':pin,'extraction_start_line':statements[0].lineno,'extraction_end_line':statements[-1].end_lineno,'program_nodes':len(space['nodes']),'source_leaves':len(space['leaves']),'edge_kinds':dict(space['kinds']),'outcomes':sum(2 if r[1]=='CD'else 1 for r in space['leaves']),'site_blocks':len(space['blocks']),'site_batches':len(space['site_modules']),'halt_leaf':[r for r in space['leaves']if r[1]=='CH'],'exact_original_site_list_equality':True,'all_leaves_covered_by_exactly_one_prefix':True,'all9batches_source_transitively_forced_fresh':True,'full_helper_or_compiler_invoked':False}
(D/'static-census.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
