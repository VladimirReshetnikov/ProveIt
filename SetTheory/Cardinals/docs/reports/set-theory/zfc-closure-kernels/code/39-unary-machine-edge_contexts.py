#!/usr/bin/env python3
"""Collect per-incoming-edge local contexts for diagnostic nonuniform elimination."""
from pathlib import Path
from collections import defaultdict,Counter
from functools import lru_cache
import importlib.util,sys,json,time,hashlib,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'support'))
from context_search import executor,program_sites,cases,check
spec=importlib.util.spec_from_file_location('gen',HERE/'upstream253/ZF/m253/tools/generate_candidate.py')
gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
tabn=gen.patched_rows(HERE/'upstream/ZF/m254/machine/zfc_254.tm')
table={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in tabn.items()}
ns=executor(table,HERE/'support/sources/symexec.py')
allcases=cases(ns,program_sites(HERE/'support/sources/Prog254.v'))
CORE={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
protect=CORE|{96}|{t for(q,b),(w,d,t)in tabn.items()if q in CORE}
ap=argparse.ArgumentParser();ap.add_argument('--radius',type=int,default=4);args=ap.parse_args()
RAD=args.radius
if RAD<1 or RAD>12:raise SystemExit("radius must be in 1..12")
W=2*RAD+1
edge_patterns=defaultdict(set);pre_patterns=defaultdict(set);affected=defaultdict(set);cur=[0];t0=time.monotonic()
# A prefix of the segment tape at each n=0,...,length covers all lengths relevant to this window,
# since all run coefficients are nonnegative integers. More than length cells are truncated.
# A register-box tail is treated as unconstrained after its fixed first zero.
@lru_cache(maxsize=200000)
def pref_profiles(segs,length):
    out=set()
    for n in range(length+1):
        seq=[]
        for s in segs:
            if len(seq)>=length:break
            if s[0]=='b':seq.append(s[1])
            elif s[0]=='r':
                _,b,a,c=s
                assert a>=0 and c>=0
                seq.extend([b]*min(length-len(seq),a*n+c))
            else:
                assert s[0]=='box'
                seq.append(0)
                missing=length-len(seq)
                for k in range(1<<missing):
                    out.add(tuple(seq)+tuple((k>>i)&1 for i in range(missing)))
                seq=None;break
        if seq is not None:out.add(tuple(seq)+tuple(0 for _ in range(length-len(seq))))
    return tuple(sorted(out))
def short(segs,length):
    out=[];minimum=0
    for s in segs:
        if minimum>=length:break
        if s[0]=='box':
            out.append(('box',));break
        out.append(tuple(s))
        if s[0]=='b':minimum+=1
        else:minimum+=s[3]
    return tuple(out)
def observe(q,form,L,R,br,exp):
    if q=='254' or form!='c' or not R or R[0][0]=='box':return
    qn=int(q)
    if qn in CORE:return # Such rows are immutable and their successors are protected.
    left=pref_profiles(short(L,RAD+1),RAD+1)
    right=pref_profiles(short(R,RAD+2),RAD+2)
    for ls in left:
        for rs in right:
            bit=rs[0];w,d,p=table[q,bit]
            if int(p) in protect:continue
            cells=list(reversed(ls))+list(rs)
            pre=cells[1:2*RAD+2]
            pre_patterns[qn,bit].add(sum(b<<i for i,b in enumerate(pre)))
            cells[RAD+1]=w
            h=RAD+1+(1 if d=='R' else -1)
            small=cells[h-RAD:h+RAD+1]
            assert len(small)==W
            pattern=sum(b<<i for i,b in enumerate(small))
            edge_patterns[qn,bit].add(pattern)
            affected[p].add(cur[0])
ns['OBSERVE']=observe
for i,c in enumerate(allcases):
    cur[0]=i;assert check(ns,c),i
ns['OBSERVE']=None
tape=set();head=0;q=5
for i in range(312975):
    b=int(head in tape);w,d,p=tabn[q,b]
    if q not in CORE and p not in protect:
        pre_patterns[q,b].add(sum(int(head-RAD+j in tape)<<j for j in range(W)))
    if w:tape.add(head)
    else:tape.discard(head)
    head+=1 if d=='R' else -1
    if q not in CORE and p not in protect:
        pattern=sum(int(head-RAD+j in tape)<<j for j in range(W))
        edge_patterns[q,b].add(pattern)
    q=p
assert(q,head,len(tape))==(96,-17,178)
target=HERE/('edge_contexts_r%d.json'%RAD)
report={'radius':RAD,'width':W,'cases':len(allcases),'boot_steps':312975,'protect':sorted(protect),
        'table':[{'q':q,'b':b,'w':w,'d':d,'t':t}for(q,b),(w,d,t)in sorted(tabn.items())],
        'edges':[{'q':q,'b':b,'target':tabn[q,b][2],'patterns':sorted(pats)}
                 for(q,b),pats in sorted(edge_patterns.items())],
        'source':'mira-emmy/busy-beaver@0d544f2a2e3c18f12278441a74b7879f31cbe856',
        'baseline_sha256':gen.CANDIDATE_SHA256,'elapsed':round(time.monotonic()-t0,3),
        'scope':'Diagnostic contexts; fixed register-box summaries reused. No new kernel proof.'}
target.write_text(json.dumps(report,indent=2)+'\n')
# Plain format for the C++ search.
lines=[f'{RAD} 254 {len(protect)} {len(edge_patterns)}',' '.join(map(str,sorted(protect)))]
for q in range(254):
    if q==8:lines.append('-1 -1 -1 -1 -1 -1');continue
    a,b=tabn[q,0],tabn[q,1]
    lines.append(f'{a[0]} {1 if a[1]=="R" else -1} {a[2]} {b[0]} {1 if b[1]=="R" else -1} {b[2]}')
for(q,b),pats in sorted(edge_patterns.items()):lines.append(' '.join(map(str,[q,b,len(pats),*sorted(pats)])))
target.with_suffix('.txt').write_text('\n'.join(lines)+'\n')
lines2=lines[:2+254]
for(q,b),pats in sorted(pre_patterns.items()):lines2.append(' '.join(map(str,[q,b,len(pats),*sorted(pats)])))
(HERE/('pre_contexts_r%d.txt'%RAD)).write_text('\n'.join(lines2)+'\n')
(HERE/('pre_contexts_r%d.json'%RAD)).write_text(json.dumps([{'q':q,'b':b,'patterns':sorted(p)}for(q,b),p in sorted(pre_patterns.items())],indent=2)+'\n')
print(json.dumps({'file':str(target),'edges':len(edge_patterns),'patterns':sum(map(len,edge_patterns.values())),
                  'elapsed':report['elapsed'],'cache':str(pref_profiles.cache_info())},indent=2))
