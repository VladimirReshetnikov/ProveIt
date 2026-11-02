#!/usr/bin/env python3
"""Independent finite check of cyclic fractional-window clean-column bound."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parents[2]
AUTHOR = BASE / 'research/ordinary12-ipra-bridge/compact44-fractional-clean-column'
SUPPORT = BASE / 'reviews/compact44-support-defect-independent-audit/audit.py'
PINS = {
    AUTHOR/'check.py': '05e34daab55e99fd38fdad059bd47f01e704ba33f194e9abf16296f0b57c4ee4',
    AUTHOR/'README.md': '68da4a72c1099418d611ca3c31a18023c5d5e76af00437a10ed8a7a14f7e5bac',
    SUPPORT: 'ea44ce7dedeea421766de652ac0b6cb35680a4f1013fd20e6047f5cc8561b3a8',
}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def rotate(word, width, length, shift):
    total = width*length
    mask = (1 << total)-1
    shift %= total
    return ((word << shift) | (word >> ((total-shift) % total))) & mask

def digit(word, width, index):
    return (word >> (width*index)) & ((1 << width)-1)

def main():
    for path, expected in PINS.items():
        need(sha(path)==expected, 'input pin '+str(path))
    parent = subprocess.run([sys.executable,'-I','-S',str(SUPPORT)], capture_output=True, text=True, timeout=20)
    need(parent.returncode == 0 and not parent.stderr, 'support audit exit')
    parent_output = json.loads(parent.stdout)
    need(parent_output['status']=='PASS_COMPACT44_SUPPORT_DEFECT_FINITE' and parent_output['support_size']==986, 'support audit output')
    # Exhaustively check an analogous complete cyclic bit machine, 4096 words,
    # all 12 shifts, and all 3 digits. This supplements the bit-range argument.
    for word in range(1 << 12):
        for shift in range(12):
            q, r = divmod(shift, 4)
            out = rotate(word,4,3,shift)
            for t in range(3):
                a=digit(word,4,(t-q)%3); b=digit(word,4,(t-q-1)%3)
                predicted=((a << r)&15) + (b >> (4-r))
                need(digit(out,4,t)==predicted, 'rotation direction/digit formula')
    L=8807; w=67; rho=1<<w
    E=(set(range(943)) | set(range(983,993)) | set(range(1003,1012)) |
       set(range(1013,1032)) | {1063,1064,1095,2195,3296})
    need(len(E)==986 and 1 in E and 1063 in E, 'support')
    caps=[0]*L
    for j in E: caps[j]=1
    caps[1]=0; caps[1063]=3
    # Classify each shift by its four source caps, then calculate maxima from
    # closed forms, independently of the author's per-digit maximizer.
    signatures={}
    for q in range(L):
        sig=tuple((caps[(t-q)%L],caps[(t-q-1)%L],caps[(t-q-2)%L]) for t in (4393,5495))
        signatures.setdefault(sig,[]).append(q)
    bound=0; count=0; maxima_witnesses=[]
    for sig, shifts in signatures.items():
        for r in range(w):
            low=(0,1<<r,0, (3<<r) if r<66 else (1<<66))
            high=tuple(c >> (w-r) for c in range(4))
            clean=[]
            for target,(a,b,c) in zip((4393,5495),sig):
                if low[a]+high[b]==0:
                    clean.append((low[b]+high[c],target))
            need(clean, 'no universal clean column: '+str((shifts[0],r)))
            current,target=min(clean)
            need(current <= rho//2, 'half-radix bound')
            count+=len(shifts)
            if current>bound:
                bound=current; maxima_witnesses=[(shifts[0],r,target)]
            elif current==bound and len(maxima_witnesses)<5:
                maxima_witnesses.append((shifts[0],r,target))
    need(count==590069 and bound==rho//2, 'case count / bound')
    anchors=(1<<(w*2195))|(1<<(w*3296))
    rot=rotate(anchors,w,L,w*2198+1)
    obstruction=[digit(rot,w,j) for j in (4392,4393,5494,5495)]
    need(obstruction==[0,2,2,0], 'counterexample')
    # At r=66 the same legal word reaches half-radix at the sole clean target.
    sharp=rotate(anchors,w,L,w*2198+66)
    sharp_digits=[digit(sharp,w,j) for j in (4392,4393,5494,5495)]
    need(sharp_digits[1]!=0 and sharp_digits[3]==0 and sharp_digits[2]==rho//2, 'sharp real-word witness')
    author_runs=[]
    for args in (['-I','-S'],['-O','-I','-S']):
        result=subprocess.run([sys.executable,*args,str(AUTHOR/'check.py')], capture_output=True,text=True,timeout=60)
        need(result.returncode==0 and not result.stderr, 'author checker exit')
        value=json.loads(result.stdout)
        need(value['status']=='PASS_COMPACT44_FRACTIONAL_CLEAN_FINITE' and value['shift_fraction_cases']==count and value['worst_case']==[2198,66,5495] and value['worst_predecessor_bound']==bound, 'author result')
        author_runs.append(result.returncode)
    for path, expected in PINS.items(): need(sha(path)==expected, 'post-check pin '+str(path))
    print(json.dumps({'status':'PASS_INDEPENDENT_FRACTIONAL_CLEAN_FINITE',
       'small_machine_words':4096,'small_machine_shifts':12,'small_machine_digits':3,
       'support_size':len(E),'cap_signatures':len(signatures),'cases':count,
       'maximum_predecessor':bound,'sample_maximum_signatures':maxima_witnesses,
       'counterexample':obstruction,'sharp_real_word_digits':sharp_digits,
       'author_normal_and_optimized_exits':author_runs,'parent_exit':parent.returncode,
       'scope':'finite external digit caps only; no actual-graph, all-model, nonstandard-length, carry or iPRA theorem'},indent=2))

if __name__=='__main__': main()
