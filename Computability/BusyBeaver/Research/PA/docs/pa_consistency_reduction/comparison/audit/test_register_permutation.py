from pathlib import Path
import sys,json,time
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;m=S.load_machine();perm=list(range(9));perm[2],perm[7]=7,2
entry={r:q for q,r in S.SKIPS.items()};patch={k:(w,d,entry[perm[S.SKIPS[z]]])for k,(w,d,z)in m.items()if k not in S.ENGINE_ROWS and z in S.SKIPS and perm[S.SKIPS[z]]!=S.SKIPS[z]};nm=m|patch;S.PHYSICAL=[perm[r]for r in S.PHYSICAL];print('patch',patch,'PHYSICAL',S.PHYSICAL,flush=True)
bad=[];passed=0;start=time.monotonic()
for i,b,br,s,t in S.contracts():
 if S.execute(nm,br,s,t)is None:bad.append((i,b))
 else:passed+=1
print('passed',passed,'failed',len(bad),bad[:30],'seconds',time.monotonic()-start,flush=True)
(out/'register_permutation_result.json').write_text(json.dumps(dict(passed=passed,failed=bad,permutation=perm,changed_rows=len(patch)),indent=2))
if not bad:(out/'register_T_H_swapped.tm').write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(nm.items())))
