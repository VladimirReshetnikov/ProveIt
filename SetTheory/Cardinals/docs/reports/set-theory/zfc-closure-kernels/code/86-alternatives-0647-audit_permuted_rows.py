#!/usr/bin/env python3
from pathlib import Path
import json,sys,hashlib,itertools
if not __debug__:raise RuntimeError('Assertions required')
OUT=Path(__file__).resolve().parent;ROOT=OUT.parent;D=ROOT/'logical_routes/permuted_rows'
r=json.loads((D/'results.json').read_text());b=json.loads((D/'best.json').read_text())
sys.path.insert(0,str(ROOT/'machine_encoding'));import specialized_axiom_compiler as s
old=s.SPEC['ax_rows']('a','h','b','c','u')
def tup(x):return tuple(tup(y)for y in x)if isinstance(x,list)else x
def remap(x,p):return(x[0],remap(x[1],p),remap(x[2],p))if isinstance(x,tuple)else p.get(x,x)
rows=tup(b['rows']);assert rows[0]==old[0]
for i,p in r['parameter_maps'].items():
 i=int(i);assert set(p)==set(p.values());assert rows[i]==remap(old[i],p)
C,G,V=s.components('original');fs=[C[2],G[1],*V];order=list(itertools.permutations(range(4)))[16]
bundle=s.L.trees([fs[i]for i in order],s.t)[1]
word=b['word'];stack,events=s.symbolic(word,1);assert tup(stack)==('old_top',)+rows+(bundle,)
assert word[:4]==[166,121,180,176] and word[-len(s.t.TAIL):]==s.t.TAIL
assert word.count(158)==1
assert s.common.expand(b['residual'],b['grammar'])==b['tokens']
lines=[x for x in(D/'candidate.tm').read_text().splitlines()if x and not x.startswith('#')];assert len(lines)==534
result={'status':'PASS_LOGICAL_REPARAMETERIZATION_AND_FINITE_ARTIFACT_CHECKS','row_maps':r['parameter_maps'],'working_states_reported':r['working_states'],'transition_rows':len(lines),'u_reads':word.count(158),'row_schemas_checked':8,'whole_symbolic_stack_checked':True,'GEN_prefix_and_control_tail_unchanged':True,'bundle_unchanged':True,'grammar_expansion_checked':True,'table_sha256':hashlib.sha256((D/'candidate.tm').read_bytes()).hexdigest(),'proof_scope':'Logical row-family equivalence; no bootstrap or full source-table endpoint certified'}
assert result['table_sha256']==r['sha256']
(OUT/'permuted_rows_independent_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
