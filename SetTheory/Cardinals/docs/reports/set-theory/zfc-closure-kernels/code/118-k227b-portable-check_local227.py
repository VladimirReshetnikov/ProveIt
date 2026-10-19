#!/usr/bin/env python3
"""Independent all-tape proofs of restored alias and final K175 -> K152 fold."""
from pathlib import Path
import hashlib,json
from check_construction import table,require
need=require
def parse(path):
 T,start=table(path);states={q for q,b in T};halts={z for w,d,z in T.values()}-states;need(len(halts)==1,'halt');return T,start,next(iter(halts))
H=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def incoming(T,state,bit):
    rows=[(q,b,w,d) for (q,b),(w,d,z) in T.items() if z==state]
    need(rows and all(w==bit and d==1 for q,b,w,d in rows),'incoming left-bit guard failure')
    return rows

def trajectory(T,state,cells,halt,limit=64):
    tape=dict(cells);h=0;seen=set();out=[];trace=[]
    for tick in range(limit):
        key=(state,h,tuple(sorted(tape.items())))
        if state==halt or h not in tape or key in seen:break
        seen.add(key);b=tape[h];w,d,z=T[state,b]
        trace.append([state,h,b,w,d,z]);tape[h]=w;h+=d;state=z
        out.append((state,h,dict(tape),list(trace)))
    return out

def join(old,new,q,newq,facts,halt,phi):
    a=trajectory(old,q,facts,halt);b=trajectory(new,newq,facts,halt)
    for y in b:
        for x in a:
            if (phi(x[0],x[1],x[2]),x[1],x[2])==(y[0],y[1],y[2]):
                need(x[3] and y[3],'nonpositive block')
                return {'old_state':q,'new_state':newq,'assumptions':facts,
                        'old_steps':len(x[3]),'new_steps':len(y[3]),
                        'old_trace':x[3],'new_trace':y[3],
                        'old_endpoint':[x[0],x[1]],'new_endpoint':[y[0],y[1]],
                        'final_cells':y[2],'unread_exterior_arbitrary':True}
    raise ValueError('no exact positive whole-tape join within explicit cells')

def alias_proof(old,new,start,halt):
    need(start not in (150,175) and set(old)==set(new),'alias domain/start mismatch')
    expected=old.copy();expected[150,1]=(1,-1,173)
    expected[155,1]=(1,1,150);expected[176,1]=(1,1,150)
    need(new==expected,'unexpected alias-stage rows')
    guard150=incoming(old,150,0)
    entries175=[(q,b,w,d) for (q,b),(w,d,z) in old.items() if z==175]
    need(entries175 and all(d==1 for q,b,w,d in entries175),'175 arrival does not establish its left tag')
    ordinary=[]
    for (q,b),(w,d,z) in old.items():
        if q in (150,175):continue
        nextz=150 if z==175 and w==1 else z
        need(new[q,b]==(w,d,nextz),'ordinary piecewise commutation failure')
        ordinary.append([q,b])
    def phi(q,h,cells):
        if q==175:
            need(h-1 in cells,'endpoint tag not explicit')
            return 150 if cells[h-1]==1 else 175
        return q
    cases=[]
    for q,tag,nq in ((150,0,150),(175,0,175),(175,1,150)):
        for bit in (0,1):cases.append(join(old,new,q,nq,{-1:tag,0:bit},halt,phi))
    return {'status':'INDEPENDENT_ALL_TAPE_PIECEWISE_ALIAS_PASS','states':len(old)//2,
            'initial_state':start,'halt':halt,'old150_incoming_guard':guard150,
            'old175_incoming_rows':entries175,'ordinary_rows':len(ordinary),
            'relation':'All states keep their label except old175 with left1 maps to new150; old175 with left0 stays175. Old150 always has left0.',
            'cases':cases,'scope':'Every binary initial tape and every initial head at the common start. Exact whole-tape positive block simulation with a left-bit-dependent state relation. Source reassociations preceding this basis are separate.'}

def fold_proof(old,new,start,halt):
    need(start not in (152,175),'exceptional initial state')
    phi=lambda q:152 if q==175 else q
    expected={(q,b):(w,d,phi(z)) for (q,b),(w,d,z) in old.items() if q!=175}
    expected[152,0]=(0,-1,159);expected[152,1]=(1,-1,169)
    need(new==expected,'unexpected final fold patch')
    incoming152=incoming(old,152,1);incoming175=incoming(old,175,0)
    ordinary=0
    for (q,b),(w,d,z) in old.items():
        if q in (152,175):continue
        need(new[q,b]==(w,d,phi(z)),'ordinary fold commutation');ordinary+=1
    cases=[]
    for q,tag in ((152,1),(175,0)):
        for bit in (0,1):cases.append(join(old,new,q,152,{-1:tag,0:bit},halt,lambda q,h,t:phi(q)))
    return {'status':'INDEPENDENT_ALL_TAPE_K175_K152_FOLD_PASS','old_states':len(old)//2,
            'new_states':len(new)//2,'initial_state':start,'halt':halt,
            'incoming152':incoming152,'incoming175':incoming175,'ordinary_rows':ordinary,
            'cases':cases,'scope':'For every binary initial tape and initial head at the common start, the restored-alias basis and final folded machine are halting-equivalent. The four positive blocks preserve all explicitly read cells and leave arbitrary exterior tape untouched.'}

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--output-dir',type=Path,required=True);args=ap.parse_args();OUT=args.output_dir;OUT.mkdir(parents=True,exist_ok=True)
    paths=[H/'local227/rotations228.klabels.tm',H/'local227/realias228.klabels.tm',H/'source_fold227_zerofix/candidate.klabels.tm']
    tables=[parse(p) for p in paths];need(len({(s,h) for t,s,h in tables})==1,'stage endpoints differ')
    O,start,halt=tables[0];A=tables[1][0];N=tables[2][0]
    alias=alias_proof(O,A,start,halt);fold=fold_proof(A,N,start,halt)
    controls=[]
    b=A.copy();b[176,1]=O[176,1]
    try:alias_proof(O,b,start,halt)
    except ValueError as error:controls.append({'name':'omit_one_alias_redirect','rejected':True,'reason':str(error)})
    else:raise ValueError('bad alias redirect accepted')
    a=A.copy();b=N.copy();a[119,1]=(0,1,152);b[119,1]=(0,1,152)
    try:fold_proof(a,b,start,halt)
    except ValueError as error:controls.append({'name':'break_final_left_tag','rejected':True,'reason':str(error)})
    else:raise ValueError('bad final guard accepted')
    result={'status':'INDEPENDENT_ALIAS_AND_FINAL_FOLD_ALL_TAPE_PASS',
            'rotation_basis_sha256':sha(paths[0]),'alias_basis_sha256':sha(paths[1]),
            'candidate227_klabels_sha256':sha(paths[2]),'checker_sha256':sha(Path(__file__)),
            'helper_sha256':sha(H/'check_construction.py'),'alias':alias,'fold':fold,'tamper_controls':controls,
            'scope':'Two local all-initial-tape equivalences on the exact supplied intermediate tables. This audit does not certify the preceding source rotations, source/theory bridge, blank startup, or full runtime; those are separate obligations.'}
    (OUT/'guard_repair227_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'alias_blocks':[[x['old_steps'],x['new_steps']] for x in alias['cases']],
                      'final_blocks':[[x['old_steps'],x['new_steps']] for x in fold['cases']],
                      'candidate_sha256':result['candidate227_klabels_sha256']},indent=2))

if __name__=='__main__':main()
