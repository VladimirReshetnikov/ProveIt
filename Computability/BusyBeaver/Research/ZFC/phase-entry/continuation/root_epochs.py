#!/usr/bin/env python3
"""Short independent relaxed root-frame census within three fixed prefixes."""
import argparse,hashlib,json,sys
from pathlib import Path
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--work',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
B=args.work.resolve()
ROOT=args.repo.resolve()
sys.path.insert(0,str(ROOT/'Computability/BusyBeaver/Research/ZFC'))
import candidate252_independent_audit as A
def frame(ones,h):
    if h-1 not in ones or min(ones)!=h-1:return None
    right=[x for x in ones if x>=h]
    if not right:return None
    header=min(right)
    if header-h<3:return None
    cursor=header+1;maximum=max(ones);values=[]
    while cursor<=maximum:
        if cursor in ones:return None
        cursor+=1;count=0
        while cursor in ones:count+=1;cursor+=1
        if not count:return None
        values.append(count-1)
    if len(values)<9:return None
    assert A.paint('',header-h,values[:9],values[9:],h)==ones
    return {'header':header,'gap':header-h,'physical':values[:9],'logical':[values[A.NEWPHYS[r]] for r in range(9)],'spares':values[9:],'whole_repaint_equal':True,'whole_ones':sorted(ones)}
results=[]
for name,file in [('baseline',ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm'),('R252',B/'R252.tm'),('L229',B/'L229.tm')]:
    data=file.read_bytes();table=A.read_table(data);q,h,ones=64,0,set();frames=[];visits=0
    for tick in range(100000):
        assert q!=254
        if q==96:
            visits+=1;f=frame(ones,h)
            if f is not None:frames.append({'step':tick,'head':h,**f})
        w,d,q=table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    if name!='baseline':
        c=json.loads((B/(name+'-relaxed.json')).read_text())
        assert (frames[0]['step'],frames[0]['head'],frames[0]['header'],frames[0]['whole_ones'])==(c['steps'],c['head'],c['header'],c['whole_ones'])
    results.append({'name':name,'fuel':100000,'table_sha256':hashlib.sha256(data).hexdigest(),'status':'fuel_cutoff','dispatch_visits':visits,'root_frames':frames,'final':{'state':q,'head':h,'whole_ones':sorted(ones)}})
out={'scope':__doc__,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'results':results}
args.output.write_text(json.dumps(out,indent=2)+'\n')
for r in results:
 print(r['name'],'frames',len(r['root_frames']),'dispatchvisits',r['dispatch_visits'])
 for f in r['root_frames'][:8]+r['root_frames'][-3:]:print(f['step'],f['head'],f['header'],f['gap'],f['logical'],f['spares'][:8])
