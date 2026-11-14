#!/usr/bin/env python3
"""Reproduce bounded local PA196 searches with pinned inputs, not a PA proof."""
from pathlib import Path
import argparse, contextlib, hashlib, importlib, io, json, subprocess, sys, time
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent


def run(args,out,err=None):
    with out.open('w') as f, (err or out.with_suffix('.stderr')).open('w') as e:
        subprocess.run(list(map(str,args)),stdout=f,stderr=e,check=True)
    return out.read_text()


def context_files(data,out,stem):
    R=data['radius'];a=out/(stem+'.txt');b=out/(stem+'-triples.txt')
    with a.open('w')as f,b.open('w')as g:
        f.write(str(R)+'\n');g.write(str(R)+'\n')
        for key,vs in data['contexts'].items():
            q,bit=map(int,key.split(','))
            f.write(f'{q} {bit} {len(vs)} '+ ' '.join(map(str,vs))+'\n')
            for bits in vs:g.write(f'{q} {bit} {bits}\n')
    return a,b


def write_table(table,path):
    path.write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n' for (q,b),(w,d,n)in sorted(table.items())))


def controls(bins,out):
    out.mkdir(exist_ok=True)
    def toy():return {(q,b):(b,1,196) for q in range(196)for b in(0,1)}
    def ctx(pred1,pred2):
        return {'radius':2,'contexts':{f'{q},{b}':[m for m in range(32)if (m>>2)&1==b and (pred1(m)if q==1 else pred2(m))]if q in(1,2)else[]for q in range(196)for b in(0,1)}}
    # Exact duplicate states must be recognized by the one- and two-row scanners.
    t=toy()
    for q in (1,2):t[q,0]=(0,1,5);t[q,1]=(1,1,6)
    tp=out/'duplicate.tm';write_table(t,tp)
    cf,ct=context_files(ctx(lambda m:True,lambda m:True),out,'duplicate-contexts')
    text=run([bins['fold_general'],tp,cf,64,1,2],out/'duplicate-one.txt')
    assert 'PASS 1 2 0 0 1 5 1' in text
    run([bins['fold_two_general'],tp,ct,out/'duplicate-two-survivors.txt',196,1,2],out/'duplicate-two.txt')
    assert 'SURVIVOR 1 2 0 1 5 1 1 6' in (out/'duplicate-two-survivors.txt').read_text()
    # Head offset -2. The new reader advances three cells, matching one old step.
    t=toy();t[0,0]=(0,1,1);t[1,0]=(0,1,5);t[2,1]=(1,1,6);t[3,0]=(0,1,4);t[4,0]=(0,1,5)
    tp=out/'shift.tm';write_table(t,tp)
    cf,_=context_files(ctx(lambda m:(m&7)==0,lambda m:bool(m&4)),out,'shift-contexts')
    text=run([bins['fold_shift'],tp,cf,64,1,2],out/'shift-positive.txt')
    assert 'PASS 1 2 0 0 1 3 3 -2' in text
    t[3,0]=(0,-1,4);write_table(t,tp)
    text=run([bins['fold_shift'],tp,cf,64,1,2],out/'shift-negative.txt')
    assert 'PASS 1 2 0 0 1 3 ' not in text
    # Adjacent-bit phase: incoming write is complemented, a three-step block restores it.
    t=toy();t[0,0]=(1,1,1);t[1,0]=(0,1,5);t[2,1]=(1,1,6);t[3,0]=(1,1,4);t[4,0]=(0,1,5)
    tp=out/'phase.tm';write_table(t,tp)
    cf,_=context_files(ctx(lambda m:(m&6)==2,lambda m:(m&6)==6),out,'phase-contexts')
    text=run([bins['fold_bitphase'],tp,cf,64,1,2],out/'phase-positive.txt')
    assert 'PASS 1 2 0 0 -1 3 3 -1' in text
    t[3,0]=(0,1,4);write_table(t,tp)
    text=run([bins['fold_bitphase'],tp,cf,64,1,2],out/'phase-negative.txt')
    assert 'PASS 1 2 0 0 -1 3 ' not in text
    return {'duplicate_one_row':True,'duplicate_two_rows':True,'head_shift_positive_and_adverse':True,'bit_phase_positive_and_adverse':True}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);p.add_argument('--radius',type=int,choices=(2,4,6),default=6);p.add_argument('--controls-only',action='store_true');p.add_argument('--quick',action='store_true',help='Check pinned inputs, all baseline symbolic cases, exact startup, and radius-two context census without compiling or searching');a=p.parse_args()
    if not __debug__:raise RuntimeError('Run without Python -O')
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=True);(out/'bin').mkdir(exist_ok=True)
    pins=json.loads((HERE/'input_pins.json').read_text())
    for name,digest in pins['files'].items():
        assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==digest, name
    if a.quick:
        import source_contexts as sc
        data=sc.collect(2)
        expected=json.loads((HERE/'receipts/contexts_r2_summary.json').read_text())
        for field in ('radius','input_table_sha256','source_contracts','opaque_or_selfloop_states','count','coarse_count'):
            assert data[field]==expected[field],field
        report={'status':'QUICK_BASELINE_PASS','input_pins_checked':True,'exact_startup_steps':58154,'context_summary':{k:v for k,v in data.items()if k!='contexts'},'scope':'Executable baseline and context checks, not a new kernel certificate or state lower bound.'}
        (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report,indent=2));return
    names=['fold_general','fold_two_general','fold_shift','fold_bitphase'];bins={}
    for name in names:
        exe=out/'bin'/name
        subprocess.run(['g++','-O3','-std=c++17',str(HERE/(name+'.cpp')),'-o',str(exe)],check=True)
        bins[name]=exe
    control=controls(bins,out/'controls');print('Positive and adverse controls passed',flush=True)
    if a.controls_only:
        (out/'receipt.json').write_text(json.dumps({'controls':control,'input_pins_checked':True},indent=2)+'\n');return
    import source_contexts as sc
    begin=time.monotonic();data=sc.collect(a.radius)
    (out/'contexts.json').write_text(json.dumps(data,indent=2)+'\n')
    cf,ct=context_files(data,out,'contexts')
    print(f"Derived {data['count']} contexts at radius {a.radius}",flush=True)
    machine=HERE/'reference/pa196/data/pa196.tm';summaries={}
    for name in ['fold_general','fold_shift','fold_bitphase']:
        text=run([bins[name],machine,cf,64],out/(name+'.txt'))
        summaries[name]={'summary':text.splitlines()[-1],'survivors':[l for l in text.splitlines()if l.startswith('PASS ')]}
        print(name, summaries[name],flush=True)
    text=run([bins['fold_two_general'],machine,ct,out/'two_rows_details.txt',196],out/'fold_two_general.txt')
    details=(out/'two_rows_details.txt').read_text().splitlines()
    summaries['fold_two_general']={'summary':text.strip(),'survivors':[l for l in details if l.startswith('SURVIVOR ')]}
    print('fold_two_general',summaries['fold_two_general'],flush=True)
    import multiple_predecessor_elimination as mp
    t=mp.read(machine);ctx={tuple(map(int,k.split(','))):v for k,v in data['contexts'].items()}
    with (out/'predecessor_progress.txt').open('w')as f,contextlib.redirect_stdout(f):
        survivors,candidates,tested,partial=mp.scan(t,ctx,a.radius,64)
    summaries['predecessor']={'deletable_states_considered':len(candidates),'tested_individual_incoming_row_actions':tested,'survivors':survivors,'partial_rows':partial}
    report={'scope':'Bounded executable searches; no new smaller machine and no PA-internal theorem established by this script.','upstream_commit':pins['upstream_commit'],'input_pins_checked':True,'controls':control,'radius':a.radius,'max_new_steps':64,'context_summary':{k:v for k,v in data.items()if k!='contexts'},'searches':summaries,'seconds':time.monotonic()-begin}
    (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n');print('Receipt:',out/'receipt.json')
if __name__=='__main__':main()
