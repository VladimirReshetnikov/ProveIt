#!/usr/bin/env python3
"""Check the exact237 startup and its unchanged clock against proved238."""
from pathlib import Path
import argparse,hashlib,json

def require(ok,msg):
    if not ok: raise ValueError(msg)

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def read(p):
    result={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,n=line.split();key=(int(q),int(b))
        require(key not in result,'Duplicate row')
        result[key]=(int(w),1 if d=='R' else -1,int(n))
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('old','new','baseline-receipt','output'):
        parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args()
    require(sha(args.old)=='069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c','Wrong238 bytes')
    require(sha(args.new)=='a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a','Wrong237 bytes')
    baseline=json.loads(args.baseline_receipt.read_text())
    require(baseline['status']=='EXACT_WHOLE_TAPE_SPARSE_DENSE_BOOTSTRAP_PASS','Wrong baseline receipt')
    require(baseline['inherited_sha256']==sha(args.old),'Baseline identity mismatch')
    old,new=read(args.old),read(args.new)
    q_old=q_new=95;h_old=h_new=0;ones_old=set();ones_new=set()
    exceptional={(98,0):0,(235,0):0,(240,1):0}
    phi=lambda q:98 if q==235 else q
    require(baseline['steps']==409835,'Wrong expected startup duration')
    for tick in range(baseline['steps']):
        require(q_new==phi(q_old) and h_new==h_old,'Checkpoint mismatch')
        b_old=int(h_old in ones_old);b_new=int(h_new in ones_new)
        require(b_old==b_new,'Read mismatch')
        key=(q_old,b_old)
        if key in exceptional: exceptional[key]+=1
        w_old,d_old,n_old=old[key];w_new,d_new,n_new=new[q_new,b_new]
        require((w_old,d_old,phi(n_old))==(w_new,d_new,n_new),'Startup ceases to be a one-step simulation')
        (ones_old.add if w_old else ones_old.discard)(h_old)
        (ones_new.add if w_new else ones_new.discard)(h_new)
        h_old+=d_old;h_new+=d_new;q_old=n_old;q_new=n_new
    require(not any(exceptional.values()),'An extra-clock row occurs during startup')
    require(ones_old==ones_new==set(baseline['one_cells']),'Whole-tape mismatch')
    require(q_old==q_new==baseline['inherited_state']==96 and h_old==h_new==baseline['head']==-5,'Endpoint mismatch')
    result={'status':'EXACT237_UNCHANGED_WHOLE_TAPE_BOOTSTRAP_PASS','steps':409835,
        'checkpoints':409836,'old_sha256':sha(args.old),'new_sha256':sha(args.new),
        'baseline_receipt_sha256':sha(args.baseline_receipt),'checker_sha256':sha(Path(__file__)),
        'exceptional_visits':{str(k):v for k,v in exceptional.items()},
        'inherited_state':96,'canonical_state':84,'head':-5,'one_cell_count':len(ones_new),
        'one_cells':sorted(ones_new),'all_other_cells_zero':True,
        'scope':'Fresh sparse two-table startup with step-by-step mapped transition equality; final whole tape equals separately proved238 sparse/dense target.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='one_cells'},indent=2))

if __name__=='__main__': main()
