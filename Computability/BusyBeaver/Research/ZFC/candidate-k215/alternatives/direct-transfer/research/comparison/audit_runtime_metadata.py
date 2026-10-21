#!/usr/bin/env python3
"""Independent audit of a saved symbolic-runtime report and case inventory.

This checker does not import the symbolic executor and does not treat saved
metadata as a replayable execution derivation. It checks the exact byte binding,
exhaustive guarded-case inventory, polynomial progress/motion summaries, actual
table rows named by the block certificates, and aggregate row/rule accounting.
"""
from pathlib import Path
import argparse, collections, gzip, hashlib, json, sys
from audit_short215 import parse, sha

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions are part of this audit; do not use Python -O.')

def strip(pc, char, count):
    positions=[i for i,c in enumerate(pc) if c==char]
    return pc[:positions[-count]] if len(positions)>=count else ''

def overflow(pc):
    return int('0' not in pc)

def main():
    ap=argparse.ArgumentParser()
    for name in ('table','source','runtime','mapping','out'):
        ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    table_bytes=a.table.read_bytes();T,start,halt=parse(table_bytes)
    source_bytes=a.source.read_bytes();S=json.loads(source_bytes)
    report_bytes=(a.runtime/'runtime.json').read_bytes()
    cases_bytes=(a.runtime/'cases.json.gz').read_bytes()
    report=json.loads(report_bytes);cases=json.loads(gzip.decompress(cases_bytes))
    mapping_bytes=a.mapping.read_bytes()
    mp={int(k):int(v)for k,v in json.loads(mapping_bytes).items()}
    assert len(set(mp.values()))==len(mp)
    for q in sorted({q for q,b in T}|{z for w,d,z in T.values()}):
        if q not in mp:mp[q]=max(mp.values())+1
    L={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T.items()}
    assert len(L)==len(T)==430 and start==0 and halt==254
    assert mp[halt]==254 and mp[84]==96
    # The final candidate's append-zero transition is bound explicitly.
    assert T[198,0]==(0,-1,40)
    assert report['table_sha256']==sha(table_bytes)
    assert report['source_sha256']==sha(source_bytes)
    assert report['status']=='PASS' and report['append']==0 and report['failures']==[]

    expected=[(i,p)for i,s in enumerate(S)for p in([False,True]if s[1]=='CD'else[False])]
    assert len(cases)==len(expected)==6151 and len(S)==4732
    got=[(x['site_index'],x['positive'])for x in cases]
    assert got==expected and len(set(got))==len(got)
    assert all(type(x['positive'])is bool for x in cases)
    covered=set();kinds=collections.Counter();motions=collections.Counter()
    for x in cases:
        pc,op,arg=S[x['site_index']]
        steps=x['symbolic_steps'];duration=x['duration'];motion=x['motion']
        assert type(steps)is int and steps>0
        assert len(duration)==len(motion)==13
        assert all(type(c)is int and c>=0 for c in duration) and duration[0]>0
        assert all(type(c)is int for c in motion)
        assert set(x['kinds'])<= {'literal','unary','list'}
        assert all(type(c)is int and c>0 for c in x['kinds'].values())
        assert sum(x['kinds'].values())==steps
        assert x['rows']==sorted(x['rows'])
        rows={tuple(r)for r in x['rows']};assert len(rows)==len(x['rows'])
        assert rows<=set(L)
        if op!='CH':
            if op=='CI' or (op=='CD' and x['positive']):n=overflow(pc)
            elif op in('CD','CB'):n=overflow(strip(pc,'0',arg if op=='CB'else 1))
            else:assert op=='CC';n=0
            assert motion==[-n]+[0]*12
        else:
            assert x['kinds']=={'literal':steps}
            assert duration==[steps]+[0]*12
            assert any(L[r][2]==mp[halt] for r in rows)
        covered.update(rows);kinds.update(x['kinds']);motions[tuple(motion)]+=1
    assert covered==set(L)

    signatures=[(73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')]
    assert len(report['blocks'])==4
    for block,sig in zip(report['blocks'],signatures):
        assert(block['entry'],block['direction'],block['before'],block['after'])==sig
        assert block['steps']=='v+2' and block['arbitrary_contexts'] is True
        clock=[0]*13;motion=[0]*13
        for event in block['trace']:
            kind,row=event[:2];q,b,w,d,z=row
            assert kind in('literal','unary') and L[q,b]==(w,d,z)
            if kind=='literal':
                assert len(event)==2;n=[1]+[0]*12
            else:
                assert len(event)==3 and q==z and d==block['direction']
                n=event[2];assert len(n)==13 and all(type(c)is int and c>=0 for c in n)
            clock=[c+v for c,v in zip(clock,n)]
            motion=[c+d*v for c,v in zip(motion,n)]
        assert clock==[2,0,1]+[0]*10
        assert motion==[block['direction']*c for c in clock]

    observed={'states':len(T)//2,'sourceleaves':len(S),'cases':len(cases),
              'expected_cases':len(expected),'rows_covered':len(covered),
              'symbolic_rules':sum(x['symbolic_steps']for x in cases),
              'min_duration':min(x['duration'][0]for x in cases)}
    assert all(report[k]==v for k,v in observed.items())
    result={'status':'SAVED_RUNTIME_METADATA_AUDIT_PASS',**observed,
            'append':0,'positive_decrement_cases':sum(p for i,p in expected),
            'case_rule_kinds':dict(kinds),'motion_counts':[{'motion':list(m),'cases':n}for m,n in sorted(motions.items())],
            'table_sha256':sha(table_bytes),'source_sha256':sha(source_bytes),
            'runtime_report_sha256':sha(report_bytes),'compressed_cases_sha256':sha(cases_bytes),
            'mapping_input_sha256':sha(mapping_bytes),'one_block_trace_rows_checked':True,
            'scope':'Inventory, exact input bindings, nonnegative positive progress metadata, expected nonhalting-case displacement, block trace row/action checks, and aggregate accounting only. Case execution traces were not retained; this audit is not an independent replay of the arbitrary-value runtime derivations and is not a proof-assistant check.'}
    (a.out/'runtime-metadata-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    (a.out/'native-to-legacy.json').write_bytes(mapping_bytes)
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
