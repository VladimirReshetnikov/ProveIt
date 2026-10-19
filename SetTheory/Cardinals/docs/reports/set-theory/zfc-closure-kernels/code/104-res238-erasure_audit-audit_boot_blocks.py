"""Independently align both literal blank runs by positive local blocks."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
BP=ROOT.parent/'combine/zfc239-research-20261019/candidate239/zfc_boundary239_old.tm'
NP=ROOT.parent/'combine/candidate238/zfc_combined238_old.tm'
def read(p):
    out={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();out[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
    return out
old=read(BP);new=read(NP)
q=h=0;q=95;nq=95;nh=0;ot=set();nt=set();oldtime=newtime=0;checkpoints=0;counts={(80,0):0,(169,0):0,(169,1):0,(91,1):0}
def advance(tab,q,h,tape,n):
    for _ in range(n):
        w,d,q=tab[q,int(h in tape)]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d
    return q,h
while oldtime<409691:
    assert nq==(80 if q==169 else q) and nh==h and ot==nt
    bit=int(h in ot);oldn=newn=1
    if (q,bit) in counts:counts[q,bit]+=1
    if q==80 and bit==0:oldn,newn=1,5
    elif q==169:oldn,newn=(1,5) if bit else (1,3)
    elif q==91 and bit==1:oldn,newn=3,11
    q,h=advance(old,q,h,ot,oldn);nq,nh=advance(new,nq,nh,nt,newn)
    oldtime+=oldn;newtime+=newn;checkpoints+=1
assert oldtime==409691 and newtime==409835
assert q==nq==96 and h==nh==-5 and ot==nt and len(ot)==351
weights={(80,0):4,(169,0):2,(169,1):4,(91,1):8}
assert newtime-oldtime==sum(counts[key]*weights[key] for key in counts)
result={'status':'EXACT_BLANK_POSITIVE_BLOCK_ALIGNMENT_PASS','baseline_sha256':hashlib.sha256(BP.read_bytes()).hexdigest(),'candidate_sha256':hashlib.sha256(NP.read_bytes()).hexdigest(),'old_steps':oldtime,'new_steps':newtime,'checkpoints':checkpoints,'counts':{f'{q}/{b}':v for (q,b),v in counts.items()},'whole_tape_compared_at_every_checkpoint':True,'endpoint':{'state':q,'head':h,'ones':sorted(ot),'all_other_cells':0}}
(ROOT/'boot_blocks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='endpoint'},indent=2))
