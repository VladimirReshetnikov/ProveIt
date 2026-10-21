"""Owned diagnostic only; never executes imported code. Reads literal Lean table data.
Produces a self-loop sweep certificate and verifies it independently on a full
finite-support tape. This is NOT a proof-assistant certificate check.
"""
import ast, json, re, hashlib
from pathlib import Path
P=Path(__file__).resolve().parent
src=P/'upstream/KDense215.lean'
s=src.read_text()
raw=s.split('def rows215')[1].split(':=',1)[1].split('\ndef act')[0].strip()
rows=ast.literal_eval(raw.replace('true','True').replace('false','False'))
labels=ast.literal_eval(s.split('def denseLabels')[1].split(':=',1)[1].split('\ndef expand')[0].strip())
assert len(rows)==len(labels)==215
# Generator: explicit list zipper. Never uses verifier's sparse absolute tape.
q=0; left=[]; right=[]; head=0; cert=[]; N=95714
for i in range(N):
    b=right[0] if right else False
    w,d,nxt=rows[q][int(b)]
    assert nxt<215
    # Only adjacent copies of the *same self-loop row* may be compressed.
    if nxt==q and cert and cert[-1][:4]==[q,int(b),int(w),int(d)] and cert[-1][5]:
        cert[-1][4]+=1
    else: cert.append([q,int(b),int(w),int(d),1,nxt==q])
    if d:
        left.insert(0,w); right=right[1:]; head+=1
    else:
        right=[left[0] if left else False,w]+right[1:]; left=left[1:]; head-=1
    q=nxt
support={head+j for j,b in enumerate(right) if b}|{head-j-1 for j,b in enumerate(left) if b}
# Verifier: sparse absolute-support tape. Sweep verifies the full read interval
# against current support, and derives next state/write/direction from table.
def verify(ops):
    state=0; h=0; ones=set(); total=0
    for row in ops:
        claimq,b,w,d,n,loop=row
        assert state==claimq and n>0 and b in (0,1) and w in (0,1) and d in (0,1)
        actual=rows[state][b]
        assert actual[:2]==(bool(w),bool(d))
        target=actual[2]
        assert target<215
        if n>1: assert target==state and loop
        lo,hi=(h,h+n) if d else (h-n+1,h+1)
        touched={x for x in ones if lo<=x<hi}
        assert len(touched)==(n if b else 0)
        ones.difference_update(touched)
        if w: ones.update(range(lo,hi))
        h+=n if d else -n; state=target; total+=n
    return state,h,ones,total
vq,vh,vs,vn=verify(cert)
assert (vq,vh,vs,vn)==(q,head,support,N)
# Exact published boot endpoint: state sparse 84, [true] on left,
# 65 blank gap, sentinel true, nine boot regs then forty spare 1 regs.
bootvs=[0,0,0,0,0,0,4,0,0]+[1]*40
endpoint=[False]*65+[True]
for v in bootvs: endpoint += [False]+[True]*(v+1)
expected={head-1}|{head+i for i,b in enumerate(endpoint) if b}
assert labels[q]==84 and support==expected
# Verify one published checkpoint, including both complete zipper sides.
cp=(P/'upstream/KBoot215Chunk000.lean').read_text()
cp1=ast.literal_eval(cp.split('def cp1')[1].split(':=',1)[1].split('\ntheorem')[0].strip().replace('true','True').replace('false','False'))
pre=[]; used=0
for row in cert:
    if used==16384: break
    x=row.copy(); x[4]=min(x[4],16384-used); pre.append(x); used+=x[4]
a,b,c,d=verify(pre)
assert labels[a]==cp1[0]
cp_support={b-i-1 for i,x in enumerate(cp1[1]) if x}|{b+i for i,x in enumerate(cp1[2]) if x}
assert c==cp_support
mutants=[]
for field,new in [(0,1),(1,1),(2,0),(3,0),(4,2)]:
    bad=[x.copy() for x in cert]; bad[0][field]=new
    try: verify(bad); mutants.append(False)
    except AssertionError: mutants.append(True)
assert all(mutants)
(P/'sweep_certificate.json').write_text(json.dumps({'format':'q, read, write, right, steps, selfloop','start':{'state':0,'head':0,'ones':[]},'ops':cert,'end':{'dense_state':q,'sparse_state':labels[q],'head':head,'ones':sorted(support)},'steps':N},separators=(',',':'))+'\n')
from collections import Counter
reduction=Counter()
for a,b,w,d,n,loop in cert:
    if n>1: reduction[labels[a]]+=n-1
out={'status':'INDEPENDENT_PYTHON_CHECK_ONLY_NOT_FORMAL_PROOF','steps':N,'macro_operations':len(cert),'sweeps_longer_than_one':sum(r[4]>1 for r in cert),'eliminated_primitive_dispatches':N-len(cert),'compression_ratio':N/len(cert),'saved_by_sparse_state':dict(reduction),'start':{'state':0,'head':0,'tape':'all zero'},'endpoint':{'dense_state':q,'sparse_state':labels[q],'absolute_head':head,'ones':len(support),'relative_left':[True],'right_length':len(endpoint),'full_support_matches':True},'first_16384_checkpoint_matches':True,'mutation_tests':mutants,'table_file_sha256':hashlib.sha256(src.read_bytes()).hexdigest()}
(P/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
