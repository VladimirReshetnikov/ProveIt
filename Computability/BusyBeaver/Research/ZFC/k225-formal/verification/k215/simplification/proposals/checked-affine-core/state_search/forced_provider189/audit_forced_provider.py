#!/usr/bin/env python3
"""Independent byte-array audit of the fixed coordinated rewrite family.

Imports no search simulator. Hashes locate possible cycles; equality of the
complete byte array is then recomputed, so hashes are not proof premises.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parent
REF=ROOT.parent if(ROOT.parent/'k215.tm').exists()else ROOT.parent/'deliverable'
sys.path.insert(0,str(REF))
from audit_spare_counterexamples import table,build,decoded,source_output,ORIGIN,SIZE
import json,hashlib,time

def prefix(rows,w,n):
    tape=build(w['site'],w['registers'],w['spares'],w['gap']);q=83;h=ORIGIN;first=None
    for tick in range(n+1):
        assert 1<h<SIZE-2
        if tick and q==83:
            f=decoded(tape,h)
            if f is not None and first is None:first=(tick,f)
        if q==215:
            assert tick==n
            return q,h,tape,first
        if tick==n:return q,h,tape,first
        b=tape[h];wri,d,z=rows[q,b];tape[h]=wri;h+=d;q=z

def check_output(rows,w,n,expected):
    q,h,tape,first=prefix(rows,w,n)
    if expected.get('halt'):
        assert q==215 and first is None
    else:
        assert q!=215 and first==(n,expected)
    return q,h,tape,first

def cycles(rows,w,limit=20000):
    tape=build(w['site'],w['registers'],w['spares'],w['gap']);q=83;h=ORIGIN;seen={}
    def weight(i):return ((i+0x9e3779b97f4a7c15)*0xbf58476d1ce4e5b9)&((1<<64)-1)
    checksum=0;ones=0
    for i,b in enumerate(tape):
        if b:checksum^=weight(i);ones+=1
    for tick in range(limit+1):
        assert 1<h<SIZE-2 and q!=215
        if tick and q==83:assert decoded(tape,h) is None
        key=(q,h,checksum,ones)
        if key in seen:
            first=seen[key];oldq,oldh,oldt,oldframe=prefix(rows,w,first)
            if oldq==q and oldh==h and oldt==tape:
                assert oldframe is None
                return dict(first_step=first,second_step=tick,period=tick-first,state=q,head=h-ORIGIN,
                            relative_one_cells=[i-h for i,b in enumerate(tape)if b])
        else:seen[key]=tick
        if tick==limit:return None
        b=tape[h];wri,d,z=rows[q,b]
        if b!=wri:checksum^=weight(h);ones+=1 if wri else -1
        tape[h]=wri;h+=d;q=z

def main():
    beg=time.time();parent=table(REF/'k215.tm')
    a=json.loads((ROOT/'forced_provider_results.json').read_text())
    b=json.loads((ROOT/'forced_provider_refinement.json').read_text())
    assert b['processed']==b['expected']==109 and not b['survivors']
    assert b['first_screen_sha256']==hashlib.sha256((ROOT/'forced_provider_results.json').read_bytes()).hexdigest()
    later={(r['provider'],r['mode']):r for r in b['results']}
    counts={};verified=[];parent_checks=0;unresolved=[]
    for c in a['results']:
        p,mode=c['provider'],c['mode'];w=c['witness']or later[p,mode]['witness']
        rows={k:v for k,v in parent.items()if k[0]!=189};rows[66,0]=(1,1,p)
        for bit in ((0,)if mode=='zero'else(1,)if mode=='one'else(0,1)):rows[p,bit]=parent[189,bit]
        assert len(rows)==428 and all(z!=189 for _,_,z in rows.values())
        check_output(parent,w,w['parent_steps'],w['parent_output']);parent_checks+=1
        want=source_output(w['site'],w['registers'])
        if want is None:assert w['parent_output'].get('halt')
        else:
            assert w['parent_output']['pc_one_positions']==want[0]
            assert w['parent_output']['registers']==want[1]
        kind=w['kind'];detail={}
        if kind=='wrong_first_dispatch':
            check_output(rows,w,w['steps'],w['actual'])
            assert want is None or w['actual']['pc_one_positions']!=want[0]or w['actual']['registers']!=want[1]
        elif kind=='unexpected_halt':
            check_output(rows,w,w['steps'],{'halt':True});assert want is not None
        elif kind=='outward_blank_ray':
            q,h,tape,first=prefix(rows,w,w['steps']);assert first is None and q!=215
            assert tape[h]==0
            wr,d,z=rows[q,0];assert z==q
            assert (d==1 and h>tape.rfind(1))or(d==-1 and h<tape.find(1))
            detail=dict(state=q,head=h-ORIGIN,row=[wr,d,z],first_one=tape.find(1)-ORIGIN,last_one=tape.rfind(1)-ORIGIN)
        elif kind=='bound':
            cyc=cycles(rows,w)
            if cyc:kind='literal_configuration_cycle';detail=cyc
            else:unresolved.append(dict(provider=p,mode=mode,site_index=w['site_index'],limit=20000))
        else:raise AssertionError(kind)
        counts[kind]=counts.get(kind,0)+1
        verified.append(dict(provider=p,mode=mode,site_index=w['site_index'],classification=kind,detail=detail))
    out=dict(status='INDEPENDENT_FIXED_FAMILY_AUDIT',tables=len(verified),parent_checks=parent_checks,
             classifications=counts,unresolved=unresolved,verified=verified,seconds=time.time()-beg,
             scope='Wrong outputs are first-clean-redispatch failures only. Exact cycles and outward rays prove divergence for their supplied primitive inputs. Bounds are not refutations. No blank-run consistency claim.',
             hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in [ROOT/'forced_provider_results.json',ROOT/'forced_provider_refinement.json',Path(__file__)]})
    (ROOT/'forced_provider_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k]for k in ['tables','parent_checks','classifications','seconds']},indent=2),flush=True)

if __name__=='__main__':main()
