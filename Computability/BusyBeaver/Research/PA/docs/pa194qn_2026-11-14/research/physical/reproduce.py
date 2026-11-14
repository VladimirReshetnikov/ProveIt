#!/usr/bin/env python3
"""Replay two bounded negative searches and the concrete relay counterexample.
Python3 plus g++ are sufficient. No checkout or network is required.
No result from this program is a state-count lower bound.
"""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, tempfile
ROOT=Path(__file__).resolve().parent

def parse(path):
    rows={}
    for l in path.read_text().splitlines():
        if not l.strip() or l.lstrip().startswith('#'):continue
        q,b,w,d,t=l.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
    return rows

def text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n' for (q,b),(w,d,t) in sorted(rows.items()))

def save(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')

def frame(path):
    ones={-1,48}|{i for i,b in enumerate(path) if int(b)};pos=49
    for value in [0]*10:
        pos+=1;ones.update(range(pos,pos+value+1));pos+=value+1
    return ones

def relay_literal(primary,relay,sites):
    initial=frame(sites[2][0]);target=frame(sites[0][0]);records={}
    for name,rows in [('primary194',primary),('relay193',relay)]:
        q,h,ones=84,0,set(initial);trace=[]
        out={'start_source_site':2,'registers':[0]*9,'spares':[0],'gap':0}
        for step in range(1,10001):
            oldq,oldh,bit=q,h,int(h in ones);w,d,q=rows[q,bit]
            trace.append([oldq,oldh,bit,w,'R' if d==1 else 'L',q])
            (ones.add if w else ones.discard)(h);h+=d
            if (q,h,ones)==(84,0,target):
                out.update(status='EXPECTED_FRAME',steps=step,head=h,ones=sorted(ones));break
            if q==84 and h==0 and {x for x in ones if x<0 or x>=48}=={x for x in initial if x<0 or x>=48}:
                out.update(status='WRONG_HEADER_FRAME',steps=step,head=h,ones=sorted(ones),differing_cells=sorted(ones^target));break
        else:raise AssertionError('Neither finite endpoint appeared')
        out['trace']=trace;records[name]=out
    assert records['primary194']['status']=='EXPECTED_FRAME' and records['primary194']['steps']==32
    assert records['relay193']['status']=='WRONG_HEADER_FRAME' and records['relay193']['steps']==54
    assert records['relay193']['differing_cells']==[3,6,8,9]
    return records

def relay_blank(relay):
    q,h,ones=74,0,set();trace=[]
    for step in range(1000):
        bit=int(h in ones);w,d,t=relay[q,bit]
        if bit==0 and t==q and (not ones or d==1 and h>max(ones) or d==-1 and h<min(ones)):
            result=dict(status='OUTWARD_RAY',steps=step,q=q,head=h,ones=sorted(ones),write=w,direction=d,trace=trace)
            assert (step,q,h,sorted(ones),w,d)==(116,35,18,[-3,1,11,12],1,1)
            return result
        trace.append([q,h,bit,w,d,t]);(ones.add if w else ones.discard)(h);q,h=t,h+d
    raise AssertionError('No ray certificate')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);ap.add_argument('--quick',action='store_true');a=ap.parse_args()
    assert __debug__,'Run without -O'
    out=a.output or Path(tempfile.mkdtemp(prefix='pa193-physical-replay-'));out.mkdir(exist_ok=True,parents=True)
    for name,digest in json.loads((ROOT/'MANIFEST.json').read_text()).items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,('checksum',name)
    primary=parse(ROOT/'data/primary194.native.tm');core=parse(ROOT/'data/runtime193.native.tm')
    expected={(q,b):(w,d,88 if t==301 else t) for (q,b),(w,d,t) in primary.items() if q!=301}
    expected.update({(88,0):(0,-1,51),(51,0):(0,1,122)})
    assert core==expected and len(core)==386
    relay=dict(core);relay.update({(36,0):(1,1,16),(16,1):(1,-1,56)})
    for q in (42,47,57,126,139,141):relay[q,1]=(0,-1,122)
    assert relay==parse(ROOT/'data/relay193.native.tm')
    sites=json.loads((ROOT/'data/primary.sites.json').read_text());ins=json.loads((ROOT/'data/primary.instructions.json').read_text())
    assert sites[2]==['00000101','continueTo',2] and ins[2]==['jump',0]
    save(out/'relay_literal_counterexample.json',relay_literal(primary,relay,sites));save(out/'relay_blank_ray.json',relay_blank(relay))
    result={'relay':{'states':193,'source_site':2,'parent_endpoint_steps':32,'wrong_endpoint_steps':54,'differing_cells':[3,6,8,9],'blank_ray_after':116},'kernel_checked':False}
    if not a.quick:
        binary=out/'two_edit_startup';subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'src/two_edit_startup.cpp'),'-o',str(binary)],check=True)
        noop=out/'noop.tsv';noop.write_text(''.join(f'{i} {q} {b} {w} {d} {t}\n' for i,((q,b),(w,d,t)) in enumerate(list(sorted(primary.items()))[:2])))
        check=subprocess.run([str(binary),str(ROOT/'data/primary194.native.tm'),str(noop),str(ROOT/'data/startup_any_frame_templates.tsv'),'200000','74'],capture_output=True,text=True,check=True)
        control=json.loads(check.stdout);assert control['steps']==58154 and control['pc']==25 and control['head']==-2 and control['gap']==0
        assert control['values']==[0,0,0,0,0,0,2,0,0]+[1]*26
        save(out/'detector_positive_control.json',control)
        search=subprocess.run([str(binary),str(ROOT/'data/runtime193.native.tm'),str(ROOT/'data/neutral_pool.tsv'),str(ROOT/'data/startup_any_frame_templates.tsv'),'200000','-1'],capture_output=True,text=True,check=True)
        (out/'two_edit_allstarts.jsonl').write_text(search.stdout);(out/'two_edit_allstarts.log').write_text(search.stderr)
        assert not search.stdout.strip()
        m=re.search(r'DONE pairs (\d+) skipped_unchanged (\d+) simulations (\d+) ticks (\d+) frames (\d+) halts (\d+) rays (\d+) limits (\d+)',search.stderr);assert m
        totals=list(map(int,m.groups()));assert totals==[52128,9127208,84266,154949514,0,649,82842,775],totals
        result['two_edit_search']=dict(zip(['pairs','unchanged_starts','representative_simulations','transitions','frames','halts','rays','bounded'],totals))
        result['two_edit_search'].update(original_starts_per_pair=193,represented_start_cases=52128*193,post_first_change_step_bound=200000)
    save(out/'replay.json',result);print(json.dumps(result,indent=2));print('Output:',out)

if __name__=='__main__':main()
