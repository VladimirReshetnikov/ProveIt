"""Own second placement and exact inherited-affine identity inventory."""
from pathlib import Path
import sys,json,hashlib,importlib.util
import tree_reader as tr
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
O=Path(__file__).parent/'v2';O.mkdir(exist_ok=False)
S=R/'Computability/BusyBeaver/Research/ZFC/candidate-k218/sites218.json'
M=R/'Computability/BusyBeaver/Research/ZFC/k219-source-search/model.py'
spec=importlib.util.spec_from_file_location('prior_own_model',M)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
tree=tr.parse(json.loads(S.read_text()));oldcfg=tr.cfg(tree)
P=(('CD',6),('CC',2))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
results=[]
for r in range(9):
 actual={};extra=[];oi=ni=0
 def convert(t):
  global oi,ni
  if t==P:
   actual[oi]=ni;actual[oi+1]=ni+3
   extra.append((ni+1,r));oi+=2;ni+=4
   return (('CD',6),((('CI',r),('CD',r)),('CC',3)))
  if tr.leaf(t):actual[oi]=ni;oi+=1;ni+=1;return t
  return convert(t[0]),convert(t[1])
 new=convert(tree);nr=tr.rows(new);nc=tr.cfg(new)
 assert oi==4744 and ni==4762 and len(extra)==9
 inverse={v:k for k,v in actual.items()};skips={j:j+2 for j,_ in extra}
 def contract(j):return inverse[skips.get(j,j)]
 for i,(effect,targets) in enumerate(oldcfg):
  j=actual[i]
  assert nc[j][0]==effect,(r,i,j,'effect')
  assert [contract(k)for k in nc[j][1]]==targets,(r,i,j,'targets')
 for j,r1 in extra:
  assert nc[j]==[['increment',r1],[j+1]]
  assert nc[j+1][0]==['decrement',r1]and nc[j+1][1][1]==j+2
 # Separate independently implemented arithmetic resolver agrees on every row.
 assert m.graph(nr)==m.arithmetic_graph(nr)
 p=O/f'post-test-pad-r{r}.sites.json';p.write_text(json.dumps(nr,separators=(',',':'))+'\n')
 results.append(dict(name=f'post-test-pad-r{r}',register=r,source=str(p),sha256=sha(p),metrics=m.metrics(new),contracted_full_CFG=True,independent_full_CFG=True,neutral_pairs=9,remaining_CD6_CC2_types=sum(n==P for n in m.nodes(new))))
 # Mathematical identity of increment followed by its matching positive decrement.
 assert results[-1]['remaining_CD6_CC2_types']==0
aff=[]
for t in m.nodes(tree):
 a=m.affine(t)
 if a is not None:aff.append(dict(tree=t,leaves=len(tr.flat(t)),matrix=a,is_identity=a==m.ID))
# This finite census is exhaustive only for the previously proved recognizer.
identities=[x for x in aff if x['is_identity']]
assert not identities
res=dict(status='NINE_POST_TEST_PADDINGS_MEASURED_NO_COMPILER',source=dict(path=str(S),sha256=sha(S)),options=results,inherited_affine_census=dict(recognized=len(aff),identities=identities,records=aff,scope='Exact all-natural affine recognizer from the previously proved source contracts; no claim that every total subtree is recognized.'),inputs=[dict(path=str(p),sha256=sha(p))for p in(S,M,Path(__file__).parent/'tree_reader.py')],script_sha256=sha(Path(__file__)),scope='Source equivalence and literal costs only. No allocator, primitive runtime, startup, or machine-state result.')
(O/'result.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(dict(options=[(x['name'],x['metrics'])for x in results],recognized_affine_blocks=len(aff),inherited_identities=len(identities))))
