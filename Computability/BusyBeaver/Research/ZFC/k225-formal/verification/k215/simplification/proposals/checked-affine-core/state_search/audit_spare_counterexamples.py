#!/usr/bin/env python3
"""Independent byte-array replay of all 59 relaxed-spare counterexamples.

No search/simulator module is imported. The fixed array includes every cell
touched, with checked bounds and an implicit infinite zero exterior. Parent
and altered tables are replayed; source effects and frame decoding are
recomputed independently. The nine cycle witnesses use literal complete
configuration equality, not hash equality or a time limit.
"""
import argparse,hashlib,json
from pathlib import Path

SIZE=65536
ORIGIN=SIZE//2
def table(path):
    rows={}
    for line in Path(path).read_text().splitlines():
        if line.strip() and not line.startswith('#'):
            x=line.split();q,b,w,z=map(int,[x[0],x[1],x[2],x[4]])
            assert x[3] in ('L','R') and b in (0,1) and w in (0,1)
            rows[q,b]=(w,-1 if x[3]=='L' else 1,z)
    assert len(rows)==430 and set(q for q,b in rows)==set(range(215))
    return rows

def build(site,regs,spares,gap):
    tape=bytearray(SIZE);tape[ORIGIN-1]=1
    for i,c in enumerate(site[0]):tape[ORIGIN+i]=int(c)
    tape[ORIGIN+64+gap]=1;p=ORIGIN+65+gap
    physical=[regs[2],regs[8],regs[1],regs[4],regs[3],regs[7],regs[0],regs[5],regs[6]]
    for n in physical+spares:
        assert n>=0;tape[p]=0;p+=1
        tape[p:p+n+1]=bytes([1])*(n+1);p+=n+1
    return tape

def decoded(tape,h):
    if tape.find(1)!=h-1:return None
    header=tape.find(1,h+52)
    if header<h+64:return None
    last=tape.rfind(1);p=header+1;values=[]
    while p<=last:
        if tape[p]!=0 or tape[p+1]!=1:return None
        p+=1;start=p
        while tape[p]:p+=1
        values.append(p-start-1)
    if p!=last+1 or len(values)<10:return None
    return {'head':h-ORIGIN,'pc_one_positions':[i-h for i in range(h,header) if tape[i]],'registers':[values[6],values[2],values[0],values[4],values[3],values[7],values[8],values[5],values[1]],'spares':values[9:],'gap':header-h-64}

def source_output(site,registers):
    counter=list(site[0]);op,arg=site[1:];regs=registers.copy()
    def cut(bit,n):
        nonlocal counter
        while counter and n:
            c=counter.pop()
            if c==bit:n-=1
        if n:counter=[]
    def plus():
        for i in range(len(counter)-1,-1,-1):
            if counter[i]=='0':counter[i]='1';break
            counter[i]='0'
    if op=='CH':return None
    if op=='CI':regs[arg]+=1;plus()
    elif op=='CD':
        if regs[arg]:regs[arg]-=1
        else:cut('0',1)
        plus()
    elif op=='CB':cut('0',arg);plus()
    elif op=='CC':cut('1',arg)
    else:raise AssertionError(op)
    return [i for i,c in enumerate(counter) if c=='1'],regs

def replay(rows,w,steps,mutation=None,cycle=None):
    tape=build(w['site'],w['registers'],w['spares'],w['gap']);q=83;h=ORIGIN;saved=None;first=None
    for tick in range(steps+1):
        assert 1<h<SIZE-2
        assert q!=215,('unexpected halt',tick)
        if tick and q==83:
            frame=decoded(tape,h)
            if frame is not None and first is None:first=(tick,frame)
        if cycle and tick==cycle['first_step']:saved=(q,h,bytes(tape))
        if tick==steps:break
        b=tape[h]
        row=mutation[1] if mutation and (q,b)==mutation[0] else rows[q,b]
        tape[h]=row[0];h+=row[1];q=row[2]
    if cycle:
        assert cycle['head_displacement']==0 and saved==(q,h,bytes(tape))
        assert cycle['state']==q and cycle['second_step']==steps and steps>cycle['first_step']
        assert first is None,'Cycle preceded by a clean dispatcher frame'
        relative=[i-h for i,b in enumerate(tape) if b]
        assert relative==cycle['relative_one_cells']
        return 'literal_configuration_cycle'
    assert first is not None and first[0]==steps,('wrong first redispatch time',first,steps)
    return first[1]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('refinement');ap.add_argument('cycles');ap.add_argument('--out',default='independent_spare_audit.json');a=ap.parse_args()
    rows=table(a.table);ref=json.loads(Path(a.refinement).read_text());cy=json.loads(Path(a.cycles).read_text());cycles={json.dumps(x['candidate'],sort_keys=True):x['result']for x in cy['resolutions']};wrong=0;loops=0;verified=[]
    assert not ref['survivors'] and len(ref['rejections'])==59
    for c in ref['rejections']:
        w=c['witness'];parent=replay(rows,w,w['parent_steps']);assert parent==w['parent_output']
        want=source_output(w['site'],w['registers']);assert want is not None
        assert parent['pc_one_positions']==want[0] and parent['registers']==want[1]
        mutation=(tuple(c['incoming']),tuple(c['replacement']));key={k:c[k]for k in ['removed','incoming','replacement']}
        assert rows[mutation[0]][2]==c['removed'] and mutation[1][2]!=c['removed']
        incoming=[k for k,v in rows.items()if k[0]!=c['removed'] and v[2]==c['removed']]
        assert incoming==[mutation[0]],'Removed state has another incoming edge'
        if 'bound' in w['actual']:
            loop=cycles[json.dumps(key,sort_keys=True)];kind=replay(rows,w,loop['second_step'],mutation,loop);loops+=1
        else:
            actual=replay(rows,w,w['steps'],mutation);assert actual==w['actual']
            assert actual['pc_one_positions']!=want[0] or actual['registers']!=want[1]
            wrong+=1;kind='wrong_logical_output'
        verified.append({**key,'site_index':w['site_index'],'kind':kind})
    result={'status':'ALL_59_COUNTEREXAMPLES_INDEPENDENTLY_VERIFIED','parent_checks':59,'wrong_decoded_outputs':wrong,'literal_configuration_cycles':loops,'verified':verified,'hashes':{Path(p).name:hashlib.sha256(Path(p).read_bytes()).hexdigest()for p in [a.table,a.refinement,a.cycles,__file__]},'scope':'Refutes the stated relaxed first-clean-redispatch primitive contract for these 59 local rewrites. The 50 wrong-output witnesses do not exclude a later-redispatch existential contract; the nine literal cycles never redispatch. Does not decide blank-run consistency calibration or all possible 214-state machines.'}
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(result['status'],wrong,loops)
if __name__=='__main__':main()
