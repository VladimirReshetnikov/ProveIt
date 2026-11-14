#!/usr/bin/env python3
"""Reproduce the finite and symbolic certificates in this packet.

This script does not rebuild Lean or infer nonhalting from a long finite run.
Python 3.10+ and the standard library suffice. Run with --extended to include
the 207-state realization of the repaired 157-node source.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'verification'))
import symbolic as S

def require(x,message):
    if not x:raise ValueError(message)
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def census(m):
    states={q for q,b in m}
    require(set(m)=={(q,b)for q in states for b in(0,1)},'two rows per working state')
    require(all(w in(0,1)and d in(-1,1)for w,d,z in m.values()),'binary alphabet and L/R moves')
    terminals={z for w,d,z in m.values()}-states
    require(terminals=={196},'unique terminal label196')
    seen={0};todo=[0]
    for q in todo:
        for b in(0,1):
            z=m[q,b][2]
            if z in states and z not in seen:seen.add(z);todo.append(z)
    return dict(states=len(states),rows=len(m),graph_reachable=len(seen),unreachable=sorted(states-seen))
def startup(m,path,bound=2000000):
    # Exact tape in absolute coordinates, not a bounded-prefix observation.
    head=-2;physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    expected={head-1,head+48}|{head+i for i,b in enumerate(path)if b}
    pos=head+49
    for v in physical:
        pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
    tape=set();q=0;h=0;used=set()
    for step in range(1,bound+1):
        key=(q,int(h in tape));require(key in m,'halt before clean startup seed')
        used.add(key);w,d,q=m[key]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d
        if q==75 and h==head and tape==expected:
            return dict(steps=step,state=q,head=h,ones=sorted(tape),physical_registers=physical),used
    raise ValueError('specified whole-tape seed not reached within explicit bound')
def verify_machine(label,path,sites,steps,expected_states):
    m=S.load_machine(path);cc=census(m)
    require(cc['states']==expected_states,'state count '+label)
    require(cc['graph_reachable']==expected_states,'graph reachability '+label)
    require(S.check_engine(m),'unchanged register-engine rows '+label)
    S.all_sites=lambda:sites
    result,observations=S.verify(m,collect=True)
    st,used=startup(m,sites[25][0]);require(st['steps']==steps,'exact startup duration '+label)
    literal=set()
    for i,branch,trace in observations:
        for kind,conf,key in trace:
            if kind!='oracle':literal.add(key)
    rec=dict(name=label,machine_sha256=sha(path),census=cc,source_sites=len(sites),contracts=result,
             startup=st,rows_covered_by_startup_and_symbolic_literals=len(literal|used),
             rows_not_covered_by_those_traces=sorted(set(m)-literal-used))
    print(label,expected_states,'states;',result['contracts'],'universal instruction cases; startup',st['steps'],flush=True)
    return rec
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--extended',action='store_true');a=ap.parse_args()
    t=time.monotonic();receipts=ROOT/'receipts';receipts.mkdir(exist_ok=True)
    baseline=ROOT/'reference/BusyBeaver/data/pa196.tm'
    require(sha(baseline)=='e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8','pinned baseline bytes')
    require(sha(ROOT/'machines/h_only_mp_h.tm')=='bd74754d75e7b8ba97fa7bfc104374de33ae603fc183ae7f08f053ab8c9ea592','combined table bytes')
    original=S.flatten(S.source_tree()[0]);records=[]
    records.append(verify_machine('Pinned PA196',baseline,original,58154,196))
    combined=freeze(json.loads((ROOT/'machines/h_only_mp_h_sites.json').read_text()))
    records.append(verify_machine('Combined196',ROOT/'machines/h_only_mp_h.tm',combined,57922,196))
    for optimize in ([],['-O']):
        subprocess.run([sys.executable,*optimize,str(ROOT/'comparison/compare_designs.py')],check=True)
        subprocess.run([sys.executable,*optimize,str(ROOT/'verification/check_commands.py')],cwd=ROOT/'verification',check=True)
        subprocess.run([sys.executable,*optimize,str(ROOT/'verification/check_source_binding.py'),
                        '--old',str(ROOT/'reference/BusyBeaver/PA196/Program.lean'),
                        '--new',str(ROOT/'machines/h_only_mp_h_sites.json'),
                        '--output',str(receipts/'source_binding_reproduced.json')],check=True)
        subprocess.run([sys.executable,*optimize,str(ROOT/'verification/check_negation.py')],check=True)
    if a.extended:
        ss=freeze(json.loads((ROOT/'research/source157/source157_tailrepair_5_sites.json').read_text()))
        require(S.instructions(ss)==S.instructions(original),'157-node layout preserves every resolved instruction')
        records.append(verify_machine('Source157 physical realization',ROOT/'research/source157/source157_tailrepair_5_trim.tm',ss,58140,207))
        ss=freeze(json.loads((ROOT/'machines/direct_negation197_sites.json').read_text()))
        records.append(verify_machine('Direct-negation197',ROOT/'machines/direct_negation197.tm',ss,57922,197))
    out=dict(status='PASS',sub196_machine_constructed=False,records=records,seconds=time.monotonic()-t,
             scope='Finite table/source/startup certificates and symbolic source-site proofs using unchanged engine lemmas. Written mathematical proof is separate. No new Lean endpoint build was performed.')
    (receipts/'reproduced.json').write_text(json.dumps(out,indent=2)+'\n')
    print('PASS. No sub-196-state machine is certified by this packet.',flush=True)
if __name__=='__main__':main()
