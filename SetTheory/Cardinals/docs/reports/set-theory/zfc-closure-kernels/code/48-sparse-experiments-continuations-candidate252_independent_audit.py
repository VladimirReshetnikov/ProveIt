#!/usr/bin/env python3
"""Independent regeneration and literal audit of the random1336 candidate252.

The full82552-step blank prefix and subsequent sampled instructions use only
literal binary rows. The8391-case affine audit remains conditional on the four
attributed register-box contracts. No Lean/Coq build, generic binary simulation,
Con(ZFC) calibration, or machine minimality claim is made here.
"""
from __future__ import annotations
import argparse
from collections import Counter,deque
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parent
PERM=(0,3,4,5,8,1,6,2,7)
PHYS=(6,7,0,2,1,8,4,3,5)
NEWPHYS=tuple(PERM[r] for r in PHYS)
SKIP=(60,44,31,56,38,40,28,64,69)
SELECTOR_INCOMING={(169,1),(173,1),(18,1),(201,1),(21,1),(25,1),(39,1),
                   (47,1),(49,1),(53,1),(65,1),(70,1),(72,1),(93,1)}
BOX_STATES={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
BOX_PAIRS={(q,b) for q in BOX_STATES for b in (0,1)}-{(3,0)}
EXPECTED_SHA='939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'


def read_table(data):
    rows={}
    for line in data.decode().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,t=line.split();key=int(q),int(b)
            assert key not in rows
            rows[key]=int(w),d,int(t)
    return rows


def encode(table):
    return ('#! start 64\n'+''.join(f'{q} {b} {w} {d} {t}\n' for(q,b),(w,d,t)in sorted(table.items()))).encode()


def increment(p):
    bits=list(p)
    while bits and bits[-1]=='1':bits.pop()
    return ''.join(bits[:-1])+ '1' if bits else None


def strip(p,bit,n):
    i=len(p)
    while n and i:
        i-=1;n-=p[i]==bit
    return p[:i]


def successor(p,op,r,zero):
    if op=='CI' or op=='CD' and not zero:return increment(p)
    if op=='CD':return increment(strip(p,'0',1))
    if op=='CB':return increment(strip(p,'0',r))
    if op=='CC':return strip(p,'1',r)
    return ''


def paint(pc,gap,registers,spares,head):
    assert len(pc)<=gap
    ones={head-1,head+gap}|{head+i for i,b in enumerate(pc) if b=='1'}
    cursor=head+gap+1
    for value in registers+spares:
        cursor+=1;ones.update(range(cursor,cursor+value+1));cursor+=value+1
    return ones


def run_prefix(table,n):
    q=64;head=0;ones=set();used=Counter();prefix9=None
    for i in range(n):
        assert q!=254,('unexpected_prefix_halt',i)
        key=q,int(head in ones);used[key]+=1;w,d,q=table[key]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=1 if d=='R' else -1
        if i==8:prefix9={'state':q,'head':head,'ones':sorted(ones)}
    return q,head,ones,used,prefix9


def graph_audit(table):
    states=sorted({q for q,_ in table});seen=set();grey=deque([64])
    while grey:
        q=grey.popleft()
        if q==254 or q in seen:continue
        seen.add(q);grey.extend(table[q,b][2] for b in (0,1))
    partition={q:0 for q in states};counts=[1]
    while True:
        labels={};new={}
        for q in states:
            signature=tuple((w,d,-1 if t==254 else partition[t])for w,d,t in (table[q,0],table[q,1]))
            new[q]=labels.setdefault(signature,len(labels))
        counts.append(len(labels))
        if new==partition:break
        partition=new
    groups={}
    for q,c in new.items():groups.setdefault(c,[]).append(q)
    return {'graph_reachable_working_states':len(seen),'unreachable_states':sorted(set(states)-seen),
            'exact_bisimulation_class_counts':counts,'nontrivial_exact_bisimulation_classes':[g for g in groups.values()if len(g)>1]}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,default=ROOT)
    parser.add_argument('--source-table',type=Path)
    parser.add_argument('--scratch',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if not __debug__:parser.error('Assertions required')
    repo=args.repo.resolve();work=args.scratch.resolve()if args.scratch else Path(tempfile.mkdtemp(prefix='candidate252-independent-'))
    if work==repo or repo in work.parents or work==Path('/'):parser.error('External scratch required')
    work.mkdir(parents=True,exist_ok=True)
    upstream=repo/'lib/jeff-busy-beaver-zfc254/ZF/m254'
    original_raw=(upstream/'machine/zfc_254.tm').read_bytes();original=read_table(original_raw)
    public={key:value for key,value in original.items()if key[0]!=8}
    public.update({(3,0):(0,'L',48),(5,0):(1,'R',97),(5,1):(1,'R',64),(49,1):(0,'R',5)})
    folded={key:(w,d,64 if t==5 else t)for key,(w,d,t)in public.items()if key[0]!=5}
    table={}
    for key,(w,d,t)in folded.items():
        if key in SELECTOR_INCOMING:t=SKIP[PERM[SKIP.index(t)]]
        table[key]=w,d,t
    data=encode(table);assert hashlib.sha256(data).hexdigest()==EXPECTED_SHA
    if args.source_table:
        assert read_table(args.source_table.read_bytes())==table
        assert args.source_table.read_bytes()==data
    (work/'candidate252-oldlabels.tm').write_bytes(data)
    states={q for q,_ in table};assert len(states)==252 and len(table)==504
    assert set(table)=={(q,b)for q in states for b in (0,1)}
    assert all(w in(0,1)and d in('L','R')and t in states|{254}for w,d,t in table.values())
    assert 254 not in states and len(BOX_PAIRS)==55
    assert all(table[key]==original[key]and original[key][2]!=5 for key in BOX_PAIRS)
    changed=[{'state':q,'read':b,'before':list(folded[q,b]),'after':list(row)}for(q,b),row in table.items()if row!=folded[q,b]]
    assert len(changed)==12 and all(x['read']==1 for x in changed)
    prog_raw=(upstream/'coq/tm/Prog254.v').read_bytes()
    text=prog_raw.decode().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',text);assert len(nodes)==6459
    sites=[]
    def visit(q,p):
        for bit,e in enumerate(nodes[q]):
            path=p+str(bit);kind,*arg=e.split()
            if kind=='CN':visit(int(arg[0]),path)
            else:sites.append((path,kind,int(arg[0])if arg else None))
    visit(0,'');assert len(sites)==6460
    def walk(p):
        q=0;path=''
        while True:
            bit=p[len(path)]if len(path)<len(p)else'0';path+=bit
            kind,*arg=nodes[q][int(bit)].split()
            if kind=='CN':q=int(arg[0])
            else:
                assert not any(b=='1'for b in p[len(path):])
                return path,kind,int(arg[0])if arg else None
    source=repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    (work/'strict_affine.py').write_bytes(source.read_bytes());sys.modules['cost_search']=SimpleNamespace()
    spec=importlib.util.spec_from_file_location('candidate252_strict',work/'strict_affine.py');strict=importlib.util.module_from_spec(spec);spec.loader.exec_module(strict)
    strings={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in table.items()}
    cases=0;overflow=0;no_stray_cases=0;minimum=10**9;kind_counts=Counter()
    for p,op,r in sites:
        for zero in ((True,False)if op=='CD'else(None,)):
            physical=NEWPHYS[r]if op in('CI','CD')else r
            branch=(physical,zero)if op=='CD'else None
            nxt=successor(p,op,r,zero)
            if op!='CH':
                # Re-decoding must consume every nonzero bit of the canonical
                # successor. walk checks the entire remaining suffix, including
                # overflow's empty path, independently of register values.
                walk(''if nxt is None else nxt);no_stray_cases+=1
            effect=('inc',physical)if op=='CI'else('dec',physical)if op=='CD'and not zero else None
            if nxt is None:right=[('r',0,1,41),('b',1),('box',('plain',effect))];overflow+=1
            else:right=[('b',int(b))for b in nxt]+[('r',0,1,40-len(nxt)),('b',1),('box',('plain',effect))]
            _,literal=strict.run(strings,p,branch,strict.canon([('b',1)],right),halt=op=='CH',fuel=1000)
            assert literal>0;minimum=min(minimum,literal);cases+=1;kind_counts[op]+=1
    assert cases==8391 and overflow==3 and no_stray_cases==8390
    q,head,ones,used,prefix9=run_prefix(table,82552)
    assert prefix9=={'state':1,'head':7,'ones':[8]}
    regs=[0]*9;spares=[0]*65;spares[8]=1
    expected=paint('',40,regs,spares,2)
    assert(q,head,ones)==(96,2,expected)and len(ones)==77
    frame={'state':96,'head':2,'path':[],'head_to_header':40,'marker':1,'header':42,
           'physical_primary':regs,'logical_primary':[0]*9,'logical_tail_zero_is_separate':True,
           'spares':spares,'spare_count':65,'spare_nonzero_indices':[8],
           'whole_one_positions':sorted(ones),'all_other_cells_zero':True,
           'left_padding10_all_zero':True,'right_padding_cell':192}
    # Direct literal instruction controls after the frame, with full tape equality.
    pc='';gap=40;instruction_trace=[]
    for instruction in range(64):
        consumed,op,r=walk(pc);assert op!='CH'
        physical=NEWPHYS[r]if op in('CI','CD')else r
        zero=regs[physical]==0 if op=='CD'else None
        nxt=successor(consumed,op,r,zero);outgap=gap+(nxt is None);outpc=''if nxt is None else nxt
        outhead=head-(nxt is None);newregs=regs.copy();newspares=spares.copy()
        if op=='CI':newregs[physical]+=1
        elif op=='CD'and not zero:newregs[physical]-=1;newspares.append(0)
        target=paint(outpc,outgap,newregs,newspares,outhead);intermediate=0
        for moves in range(1,100001):
            w,d,q=table[q,int(head in ones)]
            if w:ones.add(head)
            else:ones.discard(head)
            head+=1 if d=='R'else -1
            assert q!=254
            if q==96:
                if head==outhead and ones==target:break
                intermediate+=1
        else:raise AssertionError(('literal_instruction_fuel',instruction))
        instruction_trace.append({'instruction_index':instruction,'consumed_pc':consumed,'operation':op,
                                  'logical_register':r,'new_physical_register':physical if op in('CI','CD')else None,
                                  'zero_guard':zero,'literal_microsteps':moves,'intermediate_dispatch_visits':intermediate,
                                  'next_pc':outpc,'next_gap':outgap,'head':head,'physical_primary':newregs.copy(),
                                  'spare_count':len(newspares),'whole_tape_equal':True})
        pc,gap,regs,spares=outpc,outgap,newregs,newspares
    result={'scope':'Independent exact binary finite facts and boot/productive-instruction replays; affine cases conditional on4 attributed Box contracts. No fullbinary/refutation/ConZFC equivalence.',
            'upstream_commit':'297ab8df7e5de329605c3875b4934643b371a5e3',
            'public253_PR20_head':'0d544f2a2e3c18f12278441a74b7879f31cbe856',
            'command':[sys.executable,*sys.argv],'table_sha256':EXPECTED_SHA,'scratch':str(work),
            'input_sha256':{'original254':hashlib.sha256(original_raw).hexdigest(),'Prog254':hashlib.sha256(prog_raw).hexdigest(),'strict_checker':hashlib.sha256(source.read_bytes()).hexdigest()},
            'working_states':252,'total_rows':504,'start_label':64,'halt_label':254,
            'halt_edges':[{'state':a,'read':b,'transition':list(v)}for(a,b),v in table.items()if v[2]==254],
            'physical_permutation':list(PERM),'logical_to_physical':list(NEWPHYS),
            'physical_to_logical':[NEWPHYS.index(i)for i in range(9)],'changes_from_runtime252':changed,
            'protected_Box_pairs_unchanged':55,'protected_pairs_touch_deleted5':False,
            'affine_audit':{'passed_cases':cases,'case_kinds':dict(kind_counts),'overflow_cases':overflow,'minimum_literal_rules':minimum,
                            'nonhalting_successors_no_stray_checked':no_stray_cases},
            'literal_boot_steps':82552,'blank_prefix9':prefix9,'frame':frame,
            'boot_used_transition_pairs':len(used),'boot_used_working_states':len({a for a,b in used}),
            'literal_productive_instruction_trace':instruction_trace,'graph_audit':graph_audit(table),
            'remaining_obligations':['kernel-checked82552blankboot for this exacttable','general binarysimulation undernewphysicalorder','native theory↔ConZFC calibration/internalPA endpoint'],
            'status':'all_finite_checks_passed'}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'literal_boot_steps':82552,'frame':frame,
                      'instruction_controls':len(instruction_trace),'first_instruction_moves':instruction_trace[0]['literal_microsteps'],
                      'affine_cases':cases,'graph':result['graph_audit'],'evidence':str(args.output)},indent=2))

if __name__=='__main__':main()
