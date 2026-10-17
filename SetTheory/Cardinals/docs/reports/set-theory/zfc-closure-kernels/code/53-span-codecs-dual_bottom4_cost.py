#!/usr/bin/env python3
"""Cost complete equality logic with dual rho6 and optional literal Bottom4.

Only compiler costs are reported; no calculus/consistency calibration is
claimed. Bottom4 uses the unused numerical slot 1 as primitive falsity and
shifts membership from 4P+1 to 4P+5. All original equality schemas remain.
"""
import json,sys
from pathlib import Path
from collections import Counter
BASE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path[:0]=[str(BASE/'reference'),str(BASE/'backend')]
import recover_wade_dag as rec
import TMBuilder as backend
import theory_backend_experiment as th

def main():
    nodes,names=rec.parse_dag((BASE/'reference/Dag254.v').read_text())
    word=th.expand(nodes,1)
    old=th.emit(th.Imp(th.Ex('a',th.All('a','b')),'b'))
    new=th.emit(th.Imp('b',th.All('a',th.Ex('a','b'))))
    positions=[i for i in range(len(word)-len(old)+1) if word[i:i+len(old)]==old]
    assert len(positions)==1,positions
    position=positions[0]
    dual=word[:position]+new+word[position+len(old):]
    results=[]
    for dualize in (False,True):
        for bottom in (False,True):
            for shared in (False,True):
                b=rec.builder_from_dag(backend,nodes,names)
                b.sequence_lookup={s.seq:i for i,s in enumerate(b.sequences)}
                th.lower_program(b,nodes,dual if dualize else word,'dual_bottom4',shared=shared)
                if bottom:
                    inc=b.reg('topwff').inc
                    five=b.add_sequence((156,inc))
                    b.sequences[181].seq=(119,five)
                    b.name_sequences()
                b.generate();b.tm.gc()
                states={q for q,_ in b.tm.states}
                results.append(dict(dual_rho6=dualize,primitive_bottom4=bottom,common_sequence_extraction=shared,
                   working=len(states),decision=sum(not q[0].isdigit() for q in states),framework=sum(q[0].isdigit() for q in states)))
    out=dict(old_rho6_tokens=old,new_rho6_tokens=new,token_offset=position,macro_word_length_before=len(word),
       macro_word_length_after=len(dual),results=results,formal_calibration=False,smaller_machine_claim=False)
    (BASE/'dual_bottom4_results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
