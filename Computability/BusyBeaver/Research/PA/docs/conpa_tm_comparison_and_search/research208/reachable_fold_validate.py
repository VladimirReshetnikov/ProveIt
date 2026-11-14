from pathlib import Path
import sys,json,itertools,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'support/work/optimize196'))
import core
m,labels=core.machine();cs=[c for c in core.contracts()if not(c[0]in(3774,3775)or(c[0]==3773 and c[1][1]==False))]
opts={}
for line in(ROOT/'reachable_fold_options.txt').read_text().splitlines():
 v=list(map(int,line.split()));q,b,k=v[:3];opts[q,b]={(w,d==1,t)for w,d,t in zip(v[3::3],v[4::3],v[5::3])};assert k==len(opts[q,b])
states=[q for q in labels[:-1]if q!=84 and((q not in core.BOXSTATES)or q==113)]
found=[];candidates=[]
for x,y in itertools.combinations(states,2):
 a,b=(y,x)if x==113 else(x,y)
 if a==113:continue
 cc=[]
 for bit in(0,1):
  rr={m[a,bit]}if m[a,bit]==m[b,bit]else(opts.get((a,bit),set())&opts.get((b,bit),set()))
  rr={r for r in rr if r[2]not in(a,b)}
  if b==113 and bit==1:rr&={m[113,1]}
  cc.append(rr)
 if all(cc):candidates.append((a,b,cc))
print('PAIRS',len(candidates),flush=True)
for a,b,cc in candidates:
 for r0,r1 in itertools.product(*cc):
  rows={(q,z):(w,d,b if t==a else t)for(q,z),(w,d,t)in m.items()if q!=a};rows[b,0]=r0;rows[b,1]=r1
  res=core.validate(rows,cs);print('RESULT',a,b,r0,r1,res,flush=True)
  if res['ok']:
   data={'remove':a,'retain':b,'replacement_rows':[r0,r1],'rows':[[q,z,*v]for(q,z),v in sorted(rows.items())],'validation':res,'omitted':[[3773,[2,False]],[3774,None],[3775,None]]}
   dest=ROOT/f'reachable_candidate195_{a}_{b}.json';dest.write_text(json.dumps(data,indent=2)+'\n');found.append(str(dest))
(ROOT/'reachable_fold_result.json').write_text(json.dumps({'pair_candidates':len(candidates),'accepted_contract_candidates':found},indent=2)+'\n')
print('DONE',found,flush=True)
