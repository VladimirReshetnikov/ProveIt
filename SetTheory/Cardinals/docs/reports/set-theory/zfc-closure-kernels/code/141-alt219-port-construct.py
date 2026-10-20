#!/usr/bin/env python3
"""Deterministic literal source/table reconstruction from the pinned K219 packet.

No search tool, finite frame cache, compiler, network access or installed package
is needed. Correctness is separately established by source and runtime checks.
"""
from pathlib import Path
import argparse,hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def read_table(p):
    t={};headers=[]
    for line in Path(p).read_text().splitlines():
        if line.startswith('#! start '):headers.append(int(line.split()[-1]))
        elif line and not line.startswith('#'):
            q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
            assert (q,b)not in t and b in(0,1)and w in(0,1)and d in('L','R')
            t[q,b]=(w,d,z)
    assert headers==[0]
    return t

def table_bytes(t):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode()

def retag_source(source,paths,ordinals):
    # Disjoint right reassociation ((A,B),C) -> (A,(B,C)).
    # The declared controls are retagged after retaining leaf ordinals.
    assert all(not a.startswith(b)for a in paths for b in paths if a!=b)
    out=[];seen=set()
    for i,(p,op,a)in enumerate(source):
        matches=[r for r in paths if p.startswith(r)]
        if matches:
            assert len(matches)==1;r=matches[0];suffix=p[len(r):]
            before=next(s for s in('00','01','1')if suffix.startswith(s))
            after={'00':'0','01':'10','1':'11'}[before]
            p=r+after+suffix[len(before):];seen.add(r)
        if i in ordinals:
            assert (op,a)==('CC',2);a=3
        out.append([p,op,a])
    assert seen==set(paths)and len(ordinals)==81
    return out

def build(baseline,out):
    cfg=json.loads((ROOT/'machine/construction.json').read_text())
    old=baseline/'machine/k219.native.tm';source=baseline/'machine/sites219.json'
    assert sha(old)==cfg['upstream_native_sha256']and sha(source)==cfg['upstream_source_sha256']
    native=read_table(old);mp={int(k):v for k,v in cfg['normalization'].items()}
    states={q for q,b in native};assert not set(mp.values())&states
    normalized={(mp.get(q,q),b):(w,d,mp.get(z,z))for(q,b),(w,d,z)in native.items()}
    inverse={v:k for k,v in mp.items()}
    assert table_bytes({(inverse.get(q,q),b):(w,d,inverse.get(z,z))for(q,b),(w,d,z)in normalized.items()})==old.read_bytes()
    original=json.loads(source.read_text());reports=[]
    for name,rec in cfg['variants'].items():
        d=out/name;d.mkdir(parents=True,exist_ok=True)
        sites=[list(s)for s in original]
        if name in('retagged','composed'):
            sites=retag_source(sites,cfg['retag_rotation_paths'],cfg['retag_control_ordinals'])
        if name in('zero_terminal','composed'):
            for i in cfg['zero_terminal_ordinals']:
                assert sites[i][1:]==['CB',1];sites[i][1:]=['CD',6]
        # The discovery source files all use this compact serialization.
        (d/'sites.json').write_text(json.dumps(sites,separators=(',',':'))+'\n')
        table=dict(normalized);seen=set()
        for q,b,w,di,z in rec['patches']:
            assert(q,b)in table and(q,b)not in seen and table[q,b]!=(w,di,z)
            seen.add((q,b));table[q,b]=(w,di,z)
        (d/'k219.native.tm').write_bytes(table_bytes(table))
        assert sha(d/'sites.json')==rec['source_sha256'],('Source reconstruction mismatch',name)
        assert sha(d/'k219.native.tm')==rec['native_sha256'],('Table reconstruction mismatch',name)
        reports.append(dict(variant=name,source_sha256=rec['source_sha256'],native_sha256=rec['native_sha256'],changed_rows=len(seen)))
    seed=dict(normalized)
    zero_rows={(q,b)for q,b,w,d,z in cfg['variants']['zero_terminal']['patches']}
    for q,b,w,d,z in cfg['variants']['composed']['patches']:
        if(q,b)not in zero_rows:seed[q,b]=(w,d,z)
    (out/'composition_seed.tm').write_bytes(table_bytes(seed))
    assert sha(out/'composition_seed.tm')=='0f13d32570b0825902670c2a9f9948e834e8ff6288d79573ac46d832e698e203'
    dump(out/'construction.json',dict(status='EXACT_THREE_ALTERNATIVE_SOURCE_AND_TABLE_RECONSTRUCTION_PASS',variants=reports,source_transform='81 disjoint right rotations and exact continuation retags; eight zero-terminal substitutions; all literal locations checked'))

if __name__=='__main__':
    assert __debug__ and not sys.flags.optimize
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    build(args.baseline,args.output)
