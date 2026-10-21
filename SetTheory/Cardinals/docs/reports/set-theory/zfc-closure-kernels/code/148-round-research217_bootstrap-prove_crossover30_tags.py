#!/usr/bin/env python3
"""Owned full symbolic replay and conservative state-51 tape observer."""
from pathlib import Path
import collections, hashlib, json, sys, time
D=Path(__file__).resolve().parent/'crossover30'
ROOT=D.parent.parent
sys.path.insert(0,str(ROOT/'k223_merged_runtime_audit/runtime'))
import symbolic_runtime as S
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
table_path=D/'initialized217.native.tm'
source_path=ROOT/'research217_encoding/crossover30_primary/sites.json'
native=S.r.table(table_path)
mapping={int(a):int(b)for a,b in json.loads((ROOT/'research218_encoding/NATIVE_TO_LEGACY.json').read_text()).items()}
T={(mapping[q],b):(w,d,mapping[n])for(q,b),(w,d,n)in native.items()}
sites=json.loads(source_path.read_text())
assert len(native)==434 and len(sites)==4744
q51=mapping[51]

def fixed_prefix(atoms,n):
    """Return only bits constant for every natural valuation, else None.

    A run contributes its guaranteed constant prefix. If an unbounded tail
    would have to be crossed, no choice of a sample value is made.
    """
    result=[]
    for atom in S.normal(atoms):
        if atom==S.BLANK:
            return result+[0]*(n-len(result))
        if atom[0]!='run':
            return None
        _,bit,length=atom
        result += [bit]*min(length[0],n-len(result))
        if len(result)==n:return result
        if any(length[1:]):return None
    return None

original_step=S.State.step
context=None
observations=[]
unknown=[]
read0_count=0
read1_right_count=0
def observe_step(state,table,lemmas,clock,motion):
    global read0_count,read1_right_count
    if state.q==q51:
        state.key()
        src=state.right if state.direction==1 else state.left
        # Unknown-length one runs are accelerated by the checked kernel.
        # If their length is zero, the following read0 visit is seen next.
        if src and src[0][0]=='run' and src[0][1]==0:
            assert src[0][2][0]>=1
            read0_count+=1
            right=(fixed_prefix(state.right,2)or[None,None])[1] if state.direction==1 else (fixed_prefix(state.right,1)or[None])[0]
            if right==1:
                read1_right_count+=1
            elif right is None:
                unknown.append(dict(context=context,kind='UNKNOWN_RIGHT_NEIGHBOR',state=state.key(),clock=clock,motion=motion))
            else:
                left=fixed_prefix(state.left,6 if state.direction==1 else 7)
                if left is None:
                    unknown.append(dict(context=context,kind='UNKNOWN_LEFT_SIX',state=state.key(),clock=clock,motion=motion))
                else:
                    if state.direction==-1:
                        assert left[0]==0;left=left[1:]
                    assert len(left)==6
                    observations.append(dict(context=context,nearest_first_bits=left,
                        left6=sum(bit<<(5-i)for i,bit in enumerate(left)),clock=clock,motion=motion,
                        symbolic_state=state.key()))
    return original_step(state,table,lemmas,clock,motion)

S.State.step=observe_step
lemmas,blocks=S.prove_blocks(T)
beg=time.monotonic();cases=[];rows=set();failure=None
for i,site in enumerate(sites):
    for positive in ((False,True)if site[1]=='CD'else(False,)):
        context=dict(index=i,site=site,positive=positive)
        try:
            result=S.case(T,lemmas,site,positive)
        except (AssertionError,KeyError)as exc:
            failure=dict(context=context,error=str(exc));break
        rows.update(result.pop('rows'));result.pop('trace')
        cases.append(dict(index=i,positive=positive,**result))
    if failure:break
    if len(cases)%500==0:print('PROVED',len(cases),'SECONDS',time.monotonic()-beg,flush=True)
boot=json.loads((D/'CONTEXT_BINDING.json').read_text())['boot_exceptions']
boot_masks=sorted({e['left6']for e in boot})
decoder_masks=sorted({e['left6']for e in observations})
receipt=dict(status='ALL_INITIALIZED217_CASES_AND_CONSERVATIVE_TAGS_PASS'
             if failure is None and len(cases)==6167 and not unknown and not {m>>2 for m in boot_masks}&{m>>2 for m in decoder_masks}
             else 'RUNTIME_OR_TAG_PROOF_INCOMPLETE',
    table_sha256=H(table_path),source_sha256=H(source_path),working_states=217,table_rows=434,
    cases=len(cases),rules=sum(c['symbolic_steps']for c in cases),row_coverage=len(rows),
    minimum_duration=min(c['duration'][0]for c in cases),failure=failure,
    symbolic_q51_read0_events=read0_count,right1_events=read1_right_count,
    right0_events=len(observations),unknown_windows=unknown,boot_left6=boot_masks,
    decoder_left6=decoder_masks,boot_left4=sorted({m>>2 for m in boot_masks}),decoder_left4=sorted({m>>2 for m in decoder_masks}),observations=observations,fresh_block_certificates=blocks,
    seconds=time.monotonic()-beg,
    scope='All natural primary registers, extra gap, and nonempty finite spare lists. '
          'Observer never concretizes a symbolic length or assumes a finite-list tail. '
          'The decoder tag applies at every 51/read0/right0 visit in every proven '
          'primitive call; the five startup tags are separately exact crossover218 tapes. The nearest four bits separate their roles. '
          'Disjoint tags alone do not supply or prove a zero-state bootstrap repair.')
(D/'INITIALIZED217_TAG_CASES.json').write_text(json.dumps(cases,indent=2)+'\n')
receipt['cases_sha256']=H(D/'INITIALIZED217_TAG_CASES.json')
(D/'INITIALIZED217_TAG_PROOF.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k not in ('observations','fresh_block_certificates')},indent=2))
