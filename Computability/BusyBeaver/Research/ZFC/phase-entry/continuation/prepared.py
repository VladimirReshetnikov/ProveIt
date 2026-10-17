#!/usr/bin/env python3
"""Few literal continued-mutant controls; no original-residual substitution."""
import argparse,hashlib,importlib.util,json,sys,time
from pathlib import Path
from collections import Counter
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--case',action='append',help='t,n,k prepared values')
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
ROOT=args.repo.resolve()
BASE=ROOT/'Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(BASE))
import candidate252_independent_audit as A
import permutation252_continuations as C
raw=(BASE/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
assert hashlib.sha256(raw).hexdigest()==A.EXPECTED_SHA
old=A.read_table(raw)
new={key:(w,d,252 if q==204 else q) for key,(w,d,q) in old.items() if key[0]!=204}
assert old[172,1]==(1,'R',204) and len(new)==502
nodes=C.read_nodes(ROOT/C.PROGRAM)
def run(t,n,k,fuel=500000):
    logical=[0,t,0,0,n,0,k,0,0]
    physical=[logical[A.NEWPHYS.index(i)] for i in range(9)]
    ones=A.paint('1111111111',40,physical,[0,1,0],0)
    q,h=96,0; frames=[]; hits=[]; used=Counter(); started=time.monotonic(); outcome='fuel_cutoff'
    for tick in range(1,fuel+1):
        if q==254: outcome='halt'; break
        bit=int(h in ones)
        if (q,bit)==(172,1): hits.append({'before_tick':tick-1,'head':h})
        used[q,bit]+=1
        w,d,q=new[q,bit]
        if w: ones.add(h)
        else: ones.discard(h)
        h+=1 if d=='R' else -1
        if q!=96: continue
        fs=[x for x in C.frames(nodes,ones,h) if x['decoded']['clean']]
        if not fs: continue
        f=fs[0]
        f={'tick':tick,'head':h,**f,'logical':[f['physical_primary'][A.NEWPHYS[i]] for i in range(9)]}
        frames.append(f)
        if f['decoded']['consumed']=='000': outcome='actual_main_join'; break
    return {'input':{'t':t,'n':n,'k':k,'logical':logical,'pc':'1111111111','spares':[0,1,0]},
      'fuel':fuel,'outcome':outcome,'steps':tick,'state':q,'head':h,'ones':len(ones),
      'changed_row_hits':hits,'clean_frames':frames,'seconds':time.monotonic()-started,
      'final_whole_ones':sorted(ones)}
values=[tuple(map(int,x.split(','))) for x in args.case] if args.case else [(0,1,0),(0,1,1),(0,2,0),(1,1,0)]
cases=[run(*v) for v in values]
out={'scope':__doc__,'table_sha256':A.EXPECTED_SHA,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
  'program_sha256':hashlib.sha256((ROOT/C.PROGRAM).read_bytes()).hexdigest(),'mutation':{'delete':204,'incoming':[172,1],'replacement':[1,'R',252]},'cases':cases}
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{'input':c['input'],'outcome':c['outcome'],'steps':c['steps'],'frames':len(c['clean_frames']),
 'row_hits':len(c['changed_row_hits']),'last_frame':c['clean_frames'][-1] if c['clean_frames'] else None,'seconds':c['seconds']}for c in cases],indent=2))
