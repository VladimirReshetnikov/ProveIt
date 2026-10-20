from pathlib import Path
import sys,json,subprocess,itertools
sys.path.insert(0,str(Path(__file__).parent));import compile_eq as c
out=Path(__file__).parent/'output/permutation_matrix';out.mkdir(parents=True,exist_ok=True)
rows=c.s.sites(c.TREE);groups={}
for pc,op,arg in rows:
 if op in('CI','CD'):groups.setdefault((arg,op),[]).append(pc)
queries=[];metadata=[]
for r,j,op in itertools.product(range(9),range(9),('CI','CD')):
 ps=groups[r,op];selected=[]
 # Distinct short suffixes cheaply screen necessary prefix admissibility.
 for p in sorted(ps,key=lambda p:(len(p),p)):
  if p[-7:]not in[p0[-7:]for p0 in selected]:selected.append(p)
  if len(selected)==5:break
 for pc in selected:
  parent=next(q for q,paths in c.P.items()if pc[:-1]in paths);bit=int(pc[-1]);action=c.T[parent,bit];i=len(metadata);metadata.append((r,j,op,pc));queries.append(f'{i} {bit} 0 '+' '.join(map(str,action))+f' 1\n{pc} {op} {j}\n')
(out/'queries.in').write_text(''.join(queries));(out/'metadata.json').write_text(json.dumps(metadata,indent=2));subprocess.run([str(out.parent/'leaf_synth'),str(c.BASE/'machine/k219.native.tm'),str(out/'queries.in'),str(out/'answers.out')],check=True)
allowed={r:set(range(9))for r in range(9)};failed=[]
for line in(out/'answers.out').read_text().splitlines():
 i,ok,*action=map(int,line.split());r,j,op,pc=metadata[i]
 if not ok:allowed[r].discard(j);failed.append((r,j,op,pc))
perms=[p for p in itertools.permutations(range(9))if all(p[r]in allowed[r]for r in range(9))and{p[0],p[4]}=={0,4}]
r={'sample_queries':len(metadata),'allowed':{str(k):sorted(v)for k,v in allowed.items()},'seed_preserving_permutations':perms,'failures':failed};(out/'summary.json').write_text(json.dumps(r,indent=2));print('allowed',r['allowed'],'candidate permutations',len(perms),flush=True)
