#!/usr/bin/env python3
"""Reproduce finite local contraction screens; no global lower-bound claim."""
from pathlib import Path
import argparse,hashlib,json,subprocess,tempfile,time
ROOT=Path(__file__).resolve().parent

def read_table(p):
    rows={}
    for line in p.read_text().splitlines():
        line=line.split('#',1)[0].strip()
        if not line: continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        if (q,b) in rows or not(q in range(194) and b in (0,1) and w in (0,1) and d in ('L','R') and n in range(195)):
            raise ValueError(('invalid row',p,line))
        rows[q,b]=(w,d,n)
    if set(rows)!={(q,b) for q in range(194) for b in (0,1)}:
        raise ValueError(('incomplete table',p))
    return rows

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--direct-only',action='store_true',help='skip the more expensive two-row synthesis')
    ap.add_argument('--neutral',action='store_true',help='also replay 422 neutral preconditions and their direct-contraction screens')
    ap.add_argument('--only',help='restrict named input, for example PA194AX11QGH')
    ap.add_argument('--output',type=Path,default=ROOT/'replayed_results.json')
    args=ap.parse_args();manifest=json.loads((ROOT/'input_manifest.json').read_text());records=[]
    for item in manifest:
        p=ROOT/'inputs'/item['path'];read_table(p)
        if hashlib.sha256(p.read_bytes()).hexdigest()!=item['sha256']:raise ValueError(('input digest',p))
    with tempfile.TemporaryDirectory(prefix='pa194-contraction-') as td:
        td=Path(td)
        for tool in ['multistep_fold','tworow_fold','neutral_row']:
            subprocess.run(['g++','-O3','-std=c++17',str(ROOT/(tool+'.cpp')),'-o',str(td/tool)],check=True)
        def run(tool,p,parameters):
            tic=time.monotonic();r=subprocess.run([str(td/tool),str(p)]+parameters,capture_output=True,text=True,check=True)
            return {'scanner':tool,'parameters':parameters,'output':r.stdout,'receipt':r.stderr,'elapsed_seconds':time.monotonic()-tic}
        for item in manifest:
            if args.only and item['name']!=args.only: continue
            commands=[('multistep_fold',['5','64','128'])]
            if not args.direct_only:commands.append(('tworow_fold',['5','8','64']))
            for tool,parameters in commands:
                r=run(tool,ROOT/'inputs'/item['path'],parameters);r.update(name=item['name'],group=item['group'],path='inputs/'+item['path'],sha256=item['sha256']);records.append(r)
                if r['output'].strip():raise RuntimeError(('unexpected survivor',r))
                print(item['name'],r['receipt'].strip(),flush=True)
        if args.neutral:
            base=ROOT/'inputs/PA194.tm';r=run('neutral_row',base,['5','8','64'])
            patches=[json.loads(l) for l in r['output'].splitlines()]
            expected=[json.loads(l) for l in (ROOT/'neutral_rows.jsonl').read_text().splitlines()]
            if patches!=expected:raise RuntimeError('neutral patch catalog differs')
            print('neutral catalog:',r['receipt'].strip(),flush=True)
            records.append({'name':'PA194 neutral catalog',**r})
            rows=read_table(base)
            for i,p in enumerate(patches):
                new=dict(rows);w,d,n=p['patch'];new[p['state'],p['read']]=(w,'R' if d==1 else 'L',n)
                trial=td/'neutral_trial.tm';trial.write_text(''.join(f'{q} {b} {w} {d} {n}\n' for(q,b),(w,d,n)in sorted(new.items())))
                r=run('multistep_fold',trial,['5','64','128']);r.update(name='PA194 neutral precondition',index=i,neutral_patch=p,sha256=hashlib.sha256(trial.read_bytes()).hexdigest());records.append(r)
                if r['output'].strip():raise RuntimeError(('unexpected neutral survivor',r))
                if (i+1)%50==0 or i+1==len(patches):print('neutral preconditions checked',i+1,'/',len(patches),flush=True)
    args.output.write_text(json.dumps(records,indent=2)+'\n')
    print('All selected local searches returned no contraction.',flush=True)
if __name__=='__main__':main()
