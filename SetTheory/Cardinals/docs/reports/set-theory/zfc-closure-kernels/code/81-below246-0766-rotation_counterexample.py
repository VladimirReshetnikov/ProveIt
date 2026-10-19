"""Record a finite failure of the naive rotation245 instruction contract.

This is not a proof that blank-tape halting differs. It diagnoses the
specified source-to-binary instruction correspondence and its macro return.
"""
from pathlib import Path
import json,hashlib
import audit245_dense as A
HERE=Path(__file__).parent

def main():
    T=A.read_table(A.TABLE)
    pc='11101001001010100111000000'
    values=[0,1,0,3,5,8,13,21,34]
    expected_pc=A.advance(A.suffix_removed(pc,'0',1))[0]
    expected_head,expected=A.desired(pc,'CD',1,values,[0],40)
    tape=A.paint(pc,0,40,values,[0]);head=A.OFFSET;q=96
    events=[];return_tape=None
    for n in range(532):
        x=head-A.OFFSET
        if n in (23,24,25,26,27,28,106,129,131,149,224,247,249,267,378,531):
            events.append(dict(completed_steps=n,state=q,head=x,read=tape[head]))
        if n==378:
            assert (q,x)==(96,0)
            return_tape=tape[:]
        if n==531:assert (q,x)==(60,41)
        w,d,q=T[q,tape[head]];tape[head]=w;head+=d
    assert return_tape is not None
    diff=[i-A.OFFSET for i,(a,b) in enumerate(zip(return_tape,expected)) if a!=b]
    assert diff==[24,25]
    assert return_tape[40+A.OFFSET:]==expected[40+A.OFFSET:]
    actual_pc=''.join(str(return_tape[A.OFFSET+i]) for i in range(40)).rstrip('0')
    decoded=next((p,op,r) for p,op,r in A.source_sites() if (actual_pc+'0'*40).startswith(p))
    assert decoded==('111010010010101001110000010','CI',6)
    out=dict(status='COUNTEREXAMPLE_TO_ADVERTISED_INSTRUCTION_CONTRACT',
        table_sha256=hashlib.sha256(A.TABLE.read_bytes()).hexdigest(),
        convention='Coordinates relative to initial dispatcher head0; marker at-1; headerat40; primary blocksB(v)=0 1^(v+1) begin41; all unlisted cellszero.',
        input=dict(dispatcher=96,head=0,pc=pc,header_distance=40,
                   physical_registers=values,spares=[0],source_operation=['CD',1],
                   physical_selected_register=2,guard='register2=0'),
        first_changed_routing=dict(completed_steps=25,state=178,head=23,read=0,
                   old_row=[0,'R',23],naive_row=[0,'R',16]),
        first_macro_return=dict(completed_steps=378,state=96,head=0,
                   actual_pc=actual_pc,expected_pc=expected_pc,header_distance=40,
                   register_file_unchanged=True,spare_suffix_unchanged=True,
                   differing_cells=[dict(position=24,expected=1,actual=0),
                                    dict(position=25,expected=0,actual=1)]),
        next_selector_disagreement=dict(completed_steps=531,state=60,head=41,
                   observed_physical_selector=0,
                   declared_source_decode=list(decoded),
                   declared_source_physical_selector=8,
                   declared_source_selector_state=69),
        trace_events=events,
        claim_boundary='Refutes the proposed source/binary local instruction correspondence at its completed-operation boundary. Does not prove inequivalent blank-tape halting, impossibility of another invariant, or absence of a later revisit to an expected configuration.')
    (HERE/'rotation_counterexample.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('trace_events','convention')},indent=2))

if __name__=='__main__':main()
