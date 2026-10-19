#!/usr/bin/env python3
"""Replay every QT-rotated source instruction against the literal 242-state table.

The affine mode uses unchanged inherited box contracts; the expanded mode
re-proves the actual-table block lemmas and expands all primary registers,
with an arbitrary nonempty finite spare suffix. Both quantify gap>=64.
The universal QT source rotation is checked separately.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import argparse,json,sys,time

def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use Python -O.')
    assert __debug__, 'Assertions are required; do not use Python -O.'
    ap=argparse.ArgumentParser()
    ap.add_argument('--reference',type=Path,default=Path(__file__).resolve().parents[1]/'reference/baseline245')
    ap.add_argument('--candidate',type=Path,default=Path(__file__).resolve().parents[1]/'machine')
    ap.add_argument('--expanded',action='store_true')
    a=ap.parse_args();sys.path.insert(0,str(a.reference/'code'))
    import build_routing_machine as B
    import parametric_prefix_affine as affine
    from review_affine_source import full_inc,full_strip
    table_path=a.candidate/'zfc_context242_old.tm'
    T,start=B.rebuild.read_table(table_path)
    assert start==95 and len(T)==484
    assert sha256(table_path.read_bytes()).hexdigest()=='6b700aa713418cfe347a6ff2d0a92de7c31810d1cf69814b4684c7fb463876a0'
    assert {q for q,b in T} == {q for q,b in T if b==0} == {q for q,b in T if b==1}
    assert {t for w,d,t in T.values()}-{q for q,b in T}=={254}
    logical=json.loads((a.candidate/'sites_logical.json').read_text())
    physical=json.loads((a.candidate/'sites_physical.json').read_text())
    assert len(logical)==len(physical)==6459
    expected=sum(2 if op=='CD'else 1 for p,op,r in logical)
    assert expected==8390
    counts=Counter();rules=Counter();used=set();records=[];began=time.monotonic()
    if a.expanded:
        import full_symbolic_parametric as F
        assert F.PADDING==64
        F.m.TABLE=T
        F.m.prove_blocks();F.m.prove_word_identity()
        for i,(p,op,r)in enumerate(logical):
            for zero in ((True,False)if op=='CD'else(None,)):
                result=F.case(p,op,r,zero,[[0,9]]*9)
                for trace in result['trace']:
                    if 'state'in trace:used.add((trace['state'],trace['read']))
                    rules[trace['rule']]+=1
                counts['cases']+=1;counts['symbolic_rules']+=result['rules']
                records.append({'index':i,'pc':p,'op':op,'r':r,'zero':zero,
                    **{k:v for k,v in result.items()if k!='trace'}})
            if i%500==0:print('expanded sites',i,'cases',counts['cases'],flush=True)
        assert used <= set(T)
        assert set(T)-used == set(), ('Unexpected unused rows',set(T)-used)
        # The formerly unreachable27/1 branch is now intentionally reused.
        # The complete expanded source replay exercises every retained row.
    else:
        affine.PADDING=64
        text_table={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in T.items()}
        for i,(p,op,r)in enumerate(physical):
            for zero in ((True,False)if op=='CD'else(None,)):
                branch=(r,zero)if op=='CD'else None
                extra=0;effect=None;overflow=False
                if op=='CI':successor,overflow=full_inc(p);effect=('inc',r)
                elif op=='CD'and not zero:successor,overflow=full_inc(p);effect=('dec',r);extra=1
                elif op=='CD':successor,overflow=full_inc(full_strip(p,'0',1))
                elif op=='CB':successor,overflow=full_inc(full_strip(p,'0',r))
                elif op=='CC':successor=full_strip(p,'1',r)
                else:assert op=='CH';successor=''
                right=[('b',int(b))for b in successor]+[('r',0,1,64+extra+int(overflow)-len(successor)),('b',1),('box',('plain',effect))]
                try:
                    rc,literal=affine.run(text_table,p,branch,affine.canon([('b',1)],right),halt=op=='CH',fuel=1000)
                except Exception:
                    print('FAIL_CASE',i,p,op,r,zero,flush=True)
                    raise
                assert literal>0
                rules.update(rc);counts['cases']+=1
                records.append({'index':i,'pc':p,'op':op,'r':r,'zero':zero,
                                'symbolic_rules':sum(rc.values()),'minimum_literal_steps':literal})
    assert counts['cases']==expected
    out={'status':'PASS_UNIVERSAL_EXPANDED_RUNTIME'if a.expanded else'PASS_UNIVERSAL_AFFINE_RUNTIME',
         'complete':True,'source_leaves':len(logical),'expected_cases':expected,'counts':dict(counts),
         'frame_padding':64,'arbitrary_primary_registers':True,'arbitrary_nonempty_finite_spare_suffix':True,
         'positive_progress_checked':True,'table_sha256':sha256(table_path.read_bytes()).hexdigest(),
         'sites_logical_sha256':sha256((a.candidate/'sites_logical.json').read_bytes()).hexdigest(),
         'rules':dict(rules),'literal_rows':sorted(used) if a.expanded else None,'literal_rows_covered':len(used) if a.expanded else None,'unused_rows':sorted(set(T)-used) if a.expanded else None,'seconds':time.monotonic()-began,
         'cases':records,'limitation':'Ordinary symbolic-induction replay; no new Lean/Rocq endpoint.'}
    name='expanded-runtime.json'if a.expanded else'affine-runtime.json'
    (a.candidate.parent/'evidence'/name).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k not in('cases','literal_rows')},indent=2),flush=True)

if __name__=='__main__':main()
