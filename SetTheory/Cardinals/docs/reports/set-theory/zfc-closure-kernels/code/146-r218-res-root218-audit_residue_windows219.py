#!/usr/bin/env python3
"""Independent concrete regression of the symbolic local-window projector.

The projector is extracted by AST from its exact source without executing its
driver. Its projection is compared with a separate literal tape simulation.
This finite regression supplements, and does not replace, the mathematical
coverage argument and the complete symbolic primitive proofs.
"""
from pathlib import Path
from collections import defaultdict
from functools import lru_cache
import sys,json,ast,hashlib,time,struct
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'k220_replay/baseline/K221_Construction_2026-10-20'
sys.path.insert(0,str(BASE/'portable'));import build221 as b
sys.path.insert(0,str(BASE/'portable/runtime/vendor'));import symbolic_runtime as rt

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def next_pc(pc):
    if not pc:return '',1
    chars=list(pc)
    for i in range(len(chars)-1,-1,-1):
        if chars[i]=='0':chars[i]='1';return ''.join(chars),0
        chars[i]='0'
    return ''.join(chars),1

def cut(pc,bit,count):
    for i in range(len(pc)-1,-1,-1):
        if pc[i]==bit:
            count-=1
            if count==0:return pc[:i]
    return ''

def frame(pc,regs,gap,spares,origin=0):
    physical=[0]*9
    for logical,index in enumerate((6,2,0,4,3,7,8,5,1)):physical[index]=regs[logical]
    ones={origin-1,origin+64+gap}
    ones.update(origin+i for i,c in enumerate(pc)if c=='1')
    cursor=origin+65+gap
    for value in physical+[1]*spares:
        cursor+=1
        for _ in range(value+1):ones.add(cursor);cursor+=1
    return ones

def target(site,regs,gap,spares):
    pc,op,arg=site;regs=regs[:];delta=0
    if op=='CH':return None
    if op=='CI':regs[arg]+=1;spares+=1;nxt,shift=next_pc(pc)
    elif op=='CD'and regs[arg]>0:regs[arg]-=1;delta=1;nxt,shift=next_pc(pc)
    elif op in('CD','CB'):nxt,shift=next_pc(cut(pc,'0',arg if op=='CB'else 1))
    else:nxt=cut(pc,'1',arg);shift=0
    return 84,-shift,frame(nxt,regs,gap+delta+shift,spares,-shift)

def block_audit(L):
    records=[]
    for q,d,before,after in((73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')):
        for nblocks in range(1,13):
            beforeword=(0,1,1)if before=='B'else(1,0,1)
            afterword=(0,1,1)if after=='B'else(1,0,1)
            if d==-1:beforeword=tuple(reversed(beforeword));afterword=tuple(reversed(afterword))
            processing={d*i for i in range(3*nblocks)}
            ones={d*i for i,c in enumerate(beforeword*nblocks)if c}
            # Explicit alternating, asymmetric exterior catches stray writes;
            # the read/write-support assertion proves exterior independence.
            exterior={x for x in range(-50,51)if x not in processing and x%5 in(1,2)}
            ones|=exterior;want={d*i for i,c in enumerate(afterword*nblocks)if c}|exterior
            state=q;head=0
            for tick in range(3*nblocks):
                assert head in processing,(q,d,nblocks,tick,'read outside block')
                w,move,state=L[state,int(head in ones)]
                if w:ones.add(head)
                else:ones.discard(head)
                head+=move
                if(tick+1)%3==0:assert state==q and head==d*(tick+1)
            assert(state,head,ones)==(q,d*3*nblocks,want)
            records.append(dict(entry=q,direction=d,before=before,after=after,blocks=nblocks,steps=3*nblocks))
    return records

def main():
    started=time.monotonic();p=ROOT/'baseline219/K219_Construction_2026-10-20/machine'
    T=b.read_table((p/'k219.native.tm').read_bytes());S=json.loads((p/'sites219.json').read_text());INV=json.loads((ROOT/'machine218/abstract219.json').read_text())['domains']
    mp={int(q):int(z)for q,z in json.loads((BASE/'portable/runtime/reference_results/legacy_mapping.json').read_text()).items()}
    for q in {q for q,bit in T}|{254}:
        if q not in mp:mp[q]=q+1000
    inv={z:q for q,z in mp.items()};L={(mp[q],bit):(w,d,mp[z])for(q,bit),(w,d,z)in T.items()}
    lemmas,_=rt.prove_blocks(L);schemas=block_audit(L)
    projector=ROOT/'root218/project_residue_windows219.py';tree=ast.parse(projector.read_text())
    names={'values','runlengths','prefix','left_bits','relevant','projected_residue_patterns','collect','loop_positions','list_positions','observed'}
    definitions=[node for node in tree.body if isinstance(node,(ast.FunctionDef,ast.AsyncFunctionDef))and node.name in names]
    assert {node.name for node in definitions}==names
    env=dict(lru_cache=lru_cache,R=7,CAP=17,rt=rt,inv=inv,L=L,lemmas=lemmas,original_step=rt.State.step,stats=defaultdict(int),windows=defaultdict(set),domains=None,covered=set())
    residue_raw=(ROOT/'root218/joint_residue.bin').read_bytes()
    rn,rbase,rwords=struct.unpack_from('<III',residue_raw)
    assert (rn,rbase,rwords)==(len(S),3**9,(3**9+63)//64)
    joint=[int.from_bytes(residue_raw[12+i*rwords*8:12+(i+1)*rwords*8],'little') for i in range(rn)]
    pow3=[3**j for j in range(9)]
    digit_masks=[[sum(1<<m for m in range(rbase) if m//pow3[j]%3==d) for d in range(3)] for j in range(9)]
    env.update(JOINT=joint,POW3=pow3,DIGIT_MASKS=digit_masks,ALL_PROFILES=(1<<rbase)-1,S=S)
    exec(compile(ast.Module(body=definitions,type_ignores=[]),str(projector),'exec'),env)
    selected={0,1,3,9,29,75,150,400,895,1773,2203,4597,4603,4718,4743};first={}
    for i,site in enumerate(S):
        if INV[i]is None:continue
        first.setdefault(tuple(site[1:]),i)
        if '000000'in site[0] and len(selected)<45:selected.add(i)
    eq_paths=json.loads((ROOT/'baseline219/K219_Construction_2026-10-20/verification/construction/construction.json').read_text())['replaced_source_paths']
    selected.update(i for i,(pc,op,arg) in enumerate(S) if any(pc.startswith(p) for p in eq_paths))
    selected.update(first.values());records=[];steps_total=0;window_checks=0
    for i in sorted(selected):
        site=S[i];masks=INV[i]
        if masks is None:continue
        for positive in((False,True)if site[1]=='CD'else(False,)):
            if site[1]=='CD'and not(masks[site[2]]&(30 if positive else 1)):continue
            ds=[(),(17,)]+[env['values'](mask,positive and site[1]=='CD'and j==site[2])for j,mask in enumerate(masks)]+[(1,),(17,)]
            env['domains']=tuple(ds);env['windows']=defaultdict(set);env['covered']=set()
            env.update(i=i,site=site,masks=masks,positive=positive)
            oldstep=rt.State.step;rt.State.step=env['observed']
            try:rt.case(L,lemmas,site,positive)
            finally:rt.State.step=oldstep
            projected=env['windows']
            profiles=joint[i]
            if site[1]=='CD':
                zero=digit_masks[site[2]][0]
                profiles &= ((1<<rbase)-1)^zero if positive else zero
            if not profiles:continue
            examples=[];rem=profiles
            while rem and len(examples)<3:
                z=(rem&-rem).bit_length()-1;examples.append(z);rem &= rem-1
            examples += [profiles.bit_length()-1]
            selected_profiles=[examples[0],examples[len(examples)//2],examples[-1]]
            for mode,profile in enumerate(selected_profiles):
                regs=[]
                for j,mask in enumerate(masks):
                    residue=profile//pow3[j]%3
                    allowed=[n for n in range(80) if mask&(1<<min(n,4)) and (0 if n==0 else 1 if n%2==0 else 2)==residue]
                    if site[1]=='CD'and j==site[2]:allowed=[n for n in allowed if bool(n)==positive]
                    assert allowed
                    n=allowed[0]if mode==0 else allowed[min(len(allowed)-1,8)] if mode==1 else allowed[-1]
                    regs.append(n)
                gap=(80,104,186)[mode];spares=(130,132,156)[mode]
                ones=frame(site[0],regs,gap,spares);want=target(site,regs,gap,spares);q=84;head=0
                for tick in range(200000):
                    if tick and((want is None and q==254)or(want is not None and(q,head,ones)==want)):break
                    pattern=sum(int(head+j-7 in ones)<<j for j in range(15))
                    assert pattern in projected[q],('Uncovered concrete window',i,site,positive,mode,tick,q,head,pattern)
                    window_checks+=1;w,d,q=T[q,int(head in ones)]
                    if w:ones.add(head)
                    else:ones.discard(head)
                    head+=d
                else:raise AssertionError(('Concrete primitive did not finish',i,mode))
                steps_total+=tick;records.append(dict(index=i,positive=positive,mode=mode,steps=tick))
            print('AUDITED',i,site[1:],positive,'cases',len(records),'windows',window_checks,flush=True)
    report=dict(residue_certificate_sha256=sha(ROOT/'root218/joint_residue.bin'),status='FINITE_DIFFERENTIAL_AUDIT_PASS',projector_sha256=sha(projector),driver_sha256=sha(Path(__file__)),baseline_table_sha256=sha(p/'k219.native.tm'),source_sha256=sha(p/'sites219.json'),source_invariant_sha256=sha(ROOT/'machine218/abstract219.json'),list_schema_checks=schemas,primitive_instances=records,literal_steps=steps_total,window_membership_checks=window_checks,seconds=time.monotonic()-started,scope='Finite concrete regression supplements the mathematical projection argument. It does not establish the seeded invariant or replace the complete unbounded primitive proof.')
    out=ROOT/'root218/windows_residue219_audit.json';out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k not in('list_schema_checks','primitive_instances')},indent=2),flush=True)

if __name__=='__main__':main()
