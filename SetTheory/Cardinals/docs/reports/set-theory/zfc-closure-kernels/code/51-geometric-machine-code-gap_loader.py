#!/usr/bin/env python3
"""Ten-state gap-to-first-register transducer for the permutation252 runtime.

Input: U at the marker h-1, empty PC, gap g>=1, first register L=0,
arbitrary remaining valid register blocks and spare suffix.
Output: old96 at head h-g-3, marker h-g-4, header h-1, gap g+2,
first register L=g+1; every other register cell stays literally fixed.
The old register L is consumed into the growing unary run. A complete
instruction-entry call uses old96/read1=(0,L,U) from PC1.

The code below is literal finite verification; the accompanying invariant
note gives the mathematical argument for all gaps and suffix values.
"""
from pathlib import Path
import json, hashlib

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'inputs/permutation252_old.tm'
LABELS={'U':300,'V':301,'E':302,'F':303,'G':304,'I':305,'J':306,
        'Test':307,'Fill':308,'Past':309}

def read_table(path=SOURCE):
    out={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();out[int(q),int(b)]=int(w),d,int(t)
    return out

def loader_rows(fold_past=False):
    # The two unused rows are totalized to the preexisting halt label.
    rows={
      'U':((1,'L','V'),(0,'R','Fill')),
      'V':((0,'L','E'),(0,'R',254)),
      'E':((0,'L','F'),(1,'L','E')),
      'F':((1,'L','G'),(1,'L','F')),
      'G':((0,'R','I'),(0,'R',254)),
      'I':((0,'R','J'),(1,'R','I')),
      'J':((0,'L','Test'),(1,'R','J')),
      'Test':((1,'L',7),(0,'R','U')),
      'Fill':((1,'R','Fill'),(1,'R','Past')),
      'Past':((1,'R','Past'),(0,'L','Test')),
    }
    if fold_past:
        rows['Fill']=((1,'R','Fill'),(1,'R','V'))
        del rows['Past']
    return {(LABELS[q],b):(w,d,LABELS[t] if isinstance(t,str) else t)
            for q,actions in rows.items() for b,(w,d,t) in enumerate(actions)}

def paint(gap,values,head=0,pc=''):
    ones={head-1,head+gap}|{head+i for i,b in enumerate(pc) if b=='1'}
    cursor=head+gap+1
    for v in values:
        cursor+=1;ones.update(range(cursor,cursor+v+1));cursor+=v+1
    return ones

def simulate(table,gap,values,head=0,via_dispatch=False,fold_past=False):
    assert gap>=1 and values and values[0]==0
    expected=paint(gap+2,[gap+1]+list(values[1:]),head-gap-3)
    ones=paint(gap,values,head,pc='1' if via_dispatch else '')
    q,h=(96,head) if via_dispatch else (LABELS['U'],head-1)
    steps=2*gap*gap+19*gap+58-4*fold_past+(1 if via_dispatch else 0)
    used=set();visits=[]
    for n in range(steps):
        assert q!=254,('halt',n,q,h)
        if q==96 and n:visits.append(n)
        row=q,int(h in ones);used.add(row);w,d,q=table[row]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    assert (q,h,ones)==(96,head-gap-3,expected),('wrong endpoint',gap,q,h,steps)
    assert not visits,('early dispatcher',gap,visits)
    assert (LABELS['V'],1) not in used and (LABELS['G'],1) not in used
    return {'gap':gap,'values':values,'head':head,'via_dispatch':via_dispatch,
            'steps':steps,'output_gap':gap+2,'output_head':h,
            'output_first_register':gap+1,'all_tape_cells_equal':True,
            'used_rows':[list(k) for k in sorted(used)]}

def main(fold_past=False):
    table=read_table();table.update(loader_rows(fold_past))
    table[96,1]=(0,'L',LABELS['U'])
    tests=[]
    for g in (1,2,3,4,8,9,39,40,41,63,100,173):
        for values in ([0],[0]+[0]*7,[0,2,0,7,1,0,3,4],[0,2,0,7,1,0,3,4,0,2,1]):
            for head in (-100,0,17):
                for via in (False,True):tests.append(simulate(table,g,values,head,via,fold_past))
    unused={(LABELS['V'],1),(LABELS['G'],1)}
    count=9 if fold_past else 10
    result={'status':'PASS','scope':__doc__,'new_working_states':count,'new_rows':2*count,
      'reachable_new_rows':2*count-2,'unused_new_rows':[list(k) for k in sorted(unused)],
      'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
      'samples':len(tests),'step_formula':f'2*g*g+19*g+{54 if fold_past else 58} plus one dispatch entry',
      'tests':tests}
    name='gap_loader_9_results.json' if fold_past else 'gap_loader_results.json'
    (ROOT.parent/'results'/name).write_text(json.dumps(result,indent=2)+'\n')
    text='#! start 300\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(loader_rows(fold_past).items()))
    (ROOT.parent/'machines'/f'gap_loader_{count}_states.tm').write_text(text)
    print(json.dumps({k:result[k] for k in ('status','new_working_states','samples','step_formula')},indent=2))

if __name__=='__main__':
    import sys
    main('--fold-past' in sys.argv)
