#!/usr/bin/env python3
"""Collect universal runtime local tape contexts and exact bootstrap contexts.

Research search input, not a theorem: final candidates must be replayed by the
complete symbolic site checker and a concrete boot with a calibrated endpoint.
The upstream symbolic executor is evaluated with an instrumentation callback.
"""
from pathlib import Path
import sys, re, json, collections, importlib.util, time, os

HERE = Path(__file__).resolve().parent
UP = HERE / 'upstream/ZF'
sys.path.insert(0, str(UP / 'm254/tools/tm'))
spec = importlib.util.spec_from_file_location('candidate', UP / 'm253/tools/generate_candidate.py')
candidate = importlib.util.module_from_spec(spec); spec.loader.exec_module(candidate)
T0 = candidate.patched_rows()
T = {(str(q), b): (w,d,str(t)) for (q,b),(w,d,t) in T0.items()}
WIDTH = int(os.environ.get('ZF_CONTEXT_RADIUS', '20'))
assert 1 <= WIDTH <= 30
CORE = {0,1,2,3,6,28,31,38,40,43,44,48,56,60,63,64,69,73,75,85,95,97,109,112,131}
incoming = collections.defaultdict(list)
for (q,b), (_,_,t) in T0.items():
    if q != t: incoming[t].append((q,b))  # A deleted state's self-edges vanish.
eligible = [q for q in range(254) if q not in CORE | {5,8,96} and incoming[q]
            and all(p not in CORE for p,b in incoming[q])]
watched = {e for q in eligible for e in incoming[q]}
segments = collections.defaultdict(set)

def clip(segs, ncell):
    out=[]
    for s in segs:
        if ncell <= 0: break
        if s[0] == 'b': out.append(s); ncell -= 1
        elif s[0] == 'r':
            _,b,a,c=s; out.append(('r',b,a,min(c,ncell))); ncell -= c
        else: out.append(('box',)); break
    return tuple(out)

def observe(q,L,R):
    key = int(q), R[0][1]
    if key in watched:
        segments[key].add((clip(L,WIDTH), clip(R,WIDTH+1)))

source = (UP / 'm254/tools/tm/symexec.py').read_text().split('paths = json.load')[0]
source = source.replace("T, _ = load(sys.argv[1]); D = sys.argv[2]; D0 = int(sys.argv[3])", "T = given_T; D0 = 40")
source = source.replace("if s[0] == 'b':\n            w, d, q2 = T[(q, s[1])]", "if s[0] == 'b':\n            observe(q,L,R)\n            w, d, q2 = T[(q, s[1])]")
ns = dict(given_T=T, observe=observe)
exec(compile(source, str(UP / 'm254/tools/tm/symexec.py'), 'exec'),ns)
tabtext=(UP / 'm254/coq/tm/Prog254.v').read_text().split('Definition p254_tab')[1].split('].')[0]
pat=r'\((C[NIDBCH])(?: (\d+))?, (C[NIDBCH])(?: (\d+))?\)'
nodes=[((a,int(b or 0)),(c,int(d or 0))) for a,b,c,d in re.findall(pat,tabtext)]
assert len(nodes)==6459
REGNAMES=['nextproof','topwff','wffstack','axiomcode','param1','param2','scratch1','scratch2','prooflist']
paths=[]
def descend(e, p):
    k,n=e
    if k=='CN':
        descend(nodes[n][0],p+'0'); descend(nodes[n][1],p+'1')
    else:
        op = {'CI':lambda:f'r.{REGNAMES[n]}.inc','CD':lambda:f'r.{REGNAMES[n]}.decnz',
              'CB':lambda:f'_break.{n}','CC':lambda:f'_continue.{n}','CH':lambda:'halt'}[k]()
        paths.append(('110'+p,op))
descend(('CN',0),''); assert len(paths)==6460

def run_all():
    res=collections.Counter()
    for p,op in paths:
        Q=p[3:]
        cases=[('-',None)] if op=='halt' else [('z','dec0'),('p','dec')] if op.endswith('.decnz') else [('-', 'inc' if op.endswith('.inc') else None)]
        for br,eff in cases:
            if op.endswith('.inc') or op.endswith('.decnz') and br=='p': Q2=ns['inc'](Q)
            elif op.endswith('.decnz'): Q2=ns['inc'](ns['strip']('0',1,Q))
            elif op.startswith('_continue'): Q2=ns['strip']('1',int(op.split('.')[1]),Q)
            elif op.startswith('_break'): Q2=ns['inc'](ns['strip']('0',int(op.split('.')[1]),Q))
            else: Q2=''
            e=() if eff is None else ((eff,ns['REG'][op.split('.')[1]]),)
            if Q2 is None: exp=ns['canon']([('b',1)],[('r',0,1,41),('b',1),('box',('plain',)+e)])
            else: exp=ns['canon']([('b',1)],ns['tape_R'](Q2,0,e))
            out=ns['run']('96',[('b',1)],ns['tape_R'](Q,0,()),br,exp)
            assert out[0]==('halt' if op=='halt' else 'ok'),(p,op,out)
            res[out[0]]+=1
    return res

def expand(segs,n,k,left):
    bits=[]
    for s in segs:
        if len(bits)>=k:break
        if s[0]=='b':bits.append(s[1])
        elif s[0]=='r':bits.extend([s[1]]*min(k-len(bits),s[2]*n+s[3]))
        else:bits += [0]+[2]*(k-len(bits)-1);break
    bits += ([0] if left else [2])*(k-len(bits))
    return bits

if __name__=='__main__':
    start=time.monotonic();res=run_all()
    print('symbolic cases',dict(res),'segments',sum(map(len,segments.values())),flush=True)
    contexts=collections.defaultdict(set)
    for key,segs in segments.items():
        for L,R in segs:
            for n in range(WIDTH+1):
                contexts[key].add(tuple(expand(L,n,WIDTH,True)[::-1]+expand(R,n,WIDTH+1,False)))
    tape=set();head=0;q=5
    for step in range(312975):
        b=int(head in tape)
        if (q,b) in watched:contexts[q,b].add(tuple(int(head+i in tape) for i in range(-WIDTH,WIDTH+1)))
        w,d,q=T0[q,b]
        if w:tape.add(head)
        else:tape.discard(head)
        head += 1 if d=='R' else -1
    assert (q,head,len(tape))==(96,-17,178)
    expected={head-1,head+40};at=head+41
    for v in [0,2,0,0,0,0,5,0,0]+[0,0,1,0,0,0,0,0,1]+[0]*149:
        expected.update(range(at+1,at+v+2));at+=v+2
    assert tape==expected
    out={'width':WIDTH,'eligible':eligible,'incoming':{str(q):incoming[q] for q in eligible},
         'table':[[q,b,w,d,t] for (q,b),(w,d,t) in sorted(T0.items())],
         'contexts':{f'{q},{b}':[''.join(map(str,v)) for v in sorted(vs)] for (q,b),vs in contexts.items()},
         'summary':{'symbolic_cases':dict(res),'eligible_states':len(eligible),'watched_edges':len(watched),
                    'unique_contexts':sum(map(len,contexts.values())),'boot_steps':312975,'elapsed_seconds':time.monotonic()-start}}
    (HERE/'paths.json').write_text(json.dumps(paths))
    (HERE/'contexts.json').write_text(json.dumps(out))
    print(json.dumps(out['summary'],sort_keys=True),flush=True)
