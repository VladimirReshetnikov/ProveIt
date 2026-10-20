"""Second implementation of finite-window invariant and whole-tape fold checking.

No source compiler, construction code, or previous fold checker is imported.
The only tape cells present in the dictionary are known entry facts. Access to
an unspecified cell fails, so each accepted trace covers every infinite binary
tape extending its explicitly listed entry patch.
"""
import argparse,json,hashlib
from pathlib import Path

def read(path):
    T={};start=None
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! start '):
            assert start is None;start=int(line.split()[-1])
        elif line and not line.startswith('#'):
            q,r,w,d,z=line.split();q,r,w,z=map(int,(q,r,w,z))
            assert r in (0,1) and w in (0,1) and d in ('L','R') and (q,r) not in T
            T[q,r]=(w,1 if d=='R' else -1,z)
    assert start==0
    states={q for q,r in T}
    assert set(T)=={(q,r) for q in states for r in (0,1)}
    assert {z for w,d,z in T.values()}-states=={254}
    return T

def run(parent,candidate,folds):
    T=read(parent);records=[]
    for fold in json.loads(Path(folds).read_text()):
        keep,drop=fold['keep'],fold['delete']
        assert keep!=drop and keep not in (0,254) and drop not in (0,254)
        facts={int(q):{int(k):v for k,v in fs.items()} for q,fs in fold['invariant'].items()}
        assert not facts.get(0,{})
        assert all(q in {q for q,r in T} for q in facts)
        for (q,r),(w,d,z) in T.items():
            pre=facts.get(q,{})
            if 0 in pre and pre[0]!=r:continue
            known={**pre,0:r}
            for offset,bit in facts.get(z,{}).items():
                assert bit in (0,1)
                oldoffset=offset+d
                assert (w if oldoffset==0 else known.get(oldoffset))==bit
        phi=lambda q:keep if q==drop else q
        U={(q,r):(w,d,phi(z)) for (q,r),(w,d,z) in T.items() if q!=drop}
        U[keep,0]=tuple(fold['a0']);U[keep,1]=tuple(fold['a1'])
        U={qr:(w,d,phi(z)) for qr,(w,d,z) in U.items()}
        blocks=[]
        for q in (keep,drop):
            for r in (0,1):
                pre=facts.get(q,{})
                if 0 in pre and pre[0]!=r:continue
                tape={**pre,0:r};expected=dict(tape)
                w,d,z=T[q,r];expected[0]=w
                state,head=keep,0;trace=[]
                for step in range(1,33):
                    assert state!=254 and head in tape
                    bit=tape[head];w2,d2,z2=U[state,bit]
                    trace.append([state,head,bit,w2,d2,z2])
                    tape[head]=w2;head+=d2;state=z2
                    if (state,head,tape)==(phi(z),d,expected):break
                else:raise AssertionError('No exact positive block')
                blocks.append({'old_state':q,'read':r,'steps':step,'trace':trace})
        for (q,r),(w,d,z) in T.items():
            if q not in (keep,drop):assert U[phi(q),r]==(w,d,phi(z))
        assert len(U)==len(T)-2
        records.append({'keep':keep,'delete':drop,'entry_facts':facts,'blocks':blocks})
        T=U
    assert T==read(candidate)
    reach={0};todo=[0]
    for q in todo:
        for r in (0,1):
            z=T[q,r][2]
            if z!=254 and z not in reach:reach.add(z);todo.append(z)
    assert reach=={q for q,r in T}
    return {'status':'SECOND_IMPLEMENTATION_ALL_TAPE_FOLD_PASS','states':len(T)//2,
            'rows':len(T),'all_states_graph_reachable':True,
            'parent_sha256':hashlib.sha256(Path(parent).read_bytes()).hexdigest(),
            'candidate_sha256':hashlib.sha256(Path(candidate).read_bytes()).hexdigest(),
            'folds':records,'scope':'All initial binary tapes and head positions, from common start0. Positive finite exact whole-tape simulation blocks; no source or consistency premise.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--parent',type=Path,required=True)
    p.add_argument('--candidate',type=Path,required=True);p.add_argument('--folds',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    result=run(a.parent,a.candidate,a.folds);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='folds'},indent=2))
