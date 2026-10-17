#!/usr/bin/env python3
"""Assemble the gap-clock scheduler with the inherited literal command body.

The instruction certificate quantifies over an arbitrary affine zero gap and
all valid register blocks, conditional on the unchanged generic box contracts.
LOAD has its separate all-gap transducer proof and exact-tape harness.  This
file does not claim a verified blank-tape construction or a state record.
"""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parent.parent
import joint_rotation_search as j
import unit_loader

# Original physical index -> desired physical index. The obsolete N slot is8.
PERM=(1,3,4,5,7,0,8,2,6)
PHYS=tuple(PERM[x] for x in j.PHYS)

def make_table():
    table=j.emit(j.NODES,j.ROOT_NODE,PERM)
    table.update({(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in unit_loader.rows().items()})
    table.update({('96',0):(0,'R','310'),('96',1):(0,'L','300'),
      ('310',0):(0,'R','47'),('310',1):(1,'R','311'),
      ('311',0):(0,'R','111'),('311',1):(0,'L','20')})
    return table

def sites():
    yield '00','CD',8
    for pc,op,r in j.sites(j.NODES,201):yield '010'+pc,op,r
    yield '011','CC',2

def certify(table):
    assert all(table[p]==j.BASE253[p] for p in j.BOX_PAIRS if p[0]!='69')
    tracked=j.Tracking(table);count=0;minimum=10**9
    for p,op,r in sites():
        for zero in ((True,False) if op=='CD' else (None,)):
            physical=PHYS[r] if op in ('CI','CD') else r
            branch=(physical,zero) if op=='CD' else None
            if op=='CI' or op=='CD' and not zero:succ=j.inc(p)
            elif op=='CD':succ=j.inc(j.strip(p,'0',1))
            elif op=='CB':succ=j.inc(j.strip(p,'0',r))
            elif op=='CC':succ=j.strip(p,'1',r)
            else:succ=''
            effect=('inc',physical) if op=='CI' else ('dec',physical) if op=='CD' and not zero else None
            right=([('r',0,1,41),('b',1),('box',('plain',effect))] if succ is None else [('b',int(b)) for b in succ]+[('r',0,1,40-len(succ)),('b',1),('box',('plain',effect))])
            try:
                _,literal=j.strict.run(tracked,p,branch,j.strict.canon([('b',1)],right),halt=op=='CH',fuel=1500)
                assert literal>0;minimum=min(minimum,literal);count+=1
            except (AssertionError,KeyError) as e:
                return {'passed':False,'cases_passed':count,'failure':{'path':p,'op':op,'reg':r,'physical':physical,'zero':zero,'reason':str(e)}},tracked.used
    return {'passed':True,'cases':count,'min_literal':minimum,'maximum_source_depth':max(len(p) for p,_,_ in sites())},tracked.used

def prune(table,used,box_pairs):
    used=used|box_pairs
    retained={q for q,b in used}|{'64','96'}
    retained|={table[k][2] for k in box_pairs}
    result={}
    for (q,b),(w,d,t) in table.items():
        if q not in retained:continue
        if t not in retained|{'254'}:
            assert (q,b) not in used,((q,b),t)
            t='64'
        result[q,b]=w,d,t
    assert len(result)==2*len(retained)
    return result

def main():
    baseline=j.emit(j.NODES,j.ROOT_NODE)
    assert baseline==j.read_table(ROOT/'inputs/permutation252_old.tm')
    table=make_table();cert,used=certify(table)
    assert cert['passed'] and cert['cases']==8381
    # Neither overlay row was used by an ordinary instruction or Box contract.
    assert not ({('27',1),('33',0)} & (used|j.BOX_PAIRS))
    ordinary_used=set(used)
    int_table={(int(q),b):(w,d,int(t)) for (q,b),(w,d,t) in table.items()}
    tests=unit_loader.suite(int_table)
    used|={(str(q),b) for q,b in unit_loader.SUPPORT}
    box_pairs=j.BOX_PAIRS-{('69',0),('69',1)}
    compact=prune(table,used,box_pairs)
    assert len(compact)==506
    compact_cert,compact_used=certify(compact)
    assert compact_cert==cert
    compact_int={(int(q),b):(w,d,int(t)) for (q,b),(w,d,t) in compact.items()}
    compact_tests=unit_loader.suite(compact_int)
    assert compact_tests==tests
    # Slot8 is an unused physical block in the arbitrary spare suffix. The
    # frame still has >=9 blocks, matching inherited Box hypotheses.
    name='gap_clock_unit253_old.tm'
    note='# DIAGNOSTIC prepared-frame runtime; blank initialization is unproved.\n'
    text=note+j.text_table(compact)
    (ROOT/'machines'/name).write_text(text)
    labels=sorted({int(q) for q,b in compact})
    renumber={q:i for i,q in enumerate(labels)}
    canonical={ (str(renumber[int(q)]),b):(w,d,str(253 if t=='254' else renumber[int(t)]))
      for (q,b),(w,d,t) in compact.items() }
    canonical_text=note+'#! start '+str(renumber[64])+'\n'+''.join(
      f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in
      sorted(canonical.items(),key=lambda kv:(int(kv[0][0]),kv[0][1])))
    (ROOT/'machines/gap_clock_unit253.tm').write_text(canonical_text)
    (ROOT/'machines/renumbering.json').write_text(json.dumps(renumber,indent=2)+'\n')
    boot,boot_used=j.boot(compact,1000000)
    # An exact finite prefix gives a stronger diagnosis than a fuel cutoff.
    q,h,ones='64',0,set()
    for _ in range(102):
        w,d,q=compact[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    assert (q,h,ones)==('42',12,{4,6,10})
    assert compact['42',0]==(1,'R','42') and max(ones)<h
    escape={'steps':102,'state':'42','head':12,'ones':[4,6,10],
      'all_other_cells_zero':True,'right_half_blank':True,
      'zero_transition':[1,'R','42'],
      'conclusion':'By induction, state42 writes1 and moves right forever. The inherited blank start cannot initialize the intended program.'}
    result={'status':'PASS as a conditional prepared-frame runtime',
      'claim':'No sub252 machine or verified blank-tape initializer is asserted.',
      'source_commit':'85633fd2f57b5dca16f87667699134d1b500ebc0',
      'physical_registers':PHYS,'first_eight_logical_by_slot':[8,2,1,4,3,7,5,6],
      'register_file_hypothesis':'At least9 blocks; slots0..7 active; slot8 onward arbitrary spares.',
      'runtime_certificate':cert,'working_states':len(compact)//2,
      'new_loader_states':7,'new_shell_states':2,
      'old_overlay_rows':[[27,1],[33,0]],
      'loader_samples':len(tests),'loader_contract':'(g,L0,h) -> (g+1,Lg+1,h-g-2), PC empty; all other register cells fixed',
      'loader_time_including_dispatch':'2*g*g+15*g+40',
      'whole_pruned_table_reverified':True,'inherited_boot':boot,
      'blank_start_escape_certificate':escape,
      'old_table_sha256':hashlib.sha256(text.encode()).hexdigest(),
      'canonical_table_sha256':hashlib.sha256(canonical_text.encode()).hexdigest(),
      'removed_baseline_labels':sorted({int(q) for q,b in baseline}-{int(q) for q,b in compact}),
      'ordinary_used_rows':[list(k) for k in sorted(ordinary_used,key=lambda p:(int(p[0]),p[1]))],
      'loader_all_gap_support':[list(k) for k in sorted(unit_loader.SUPPORT)],
      'protected_box_rows':[list(k) for k in sorted(box_pairs,key=lambda p:(int(p[0]),p[1]))]}
    (ROOT/'results/assembly_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if not k.endswith('_rows') and k!='loader_all_gap_support'},indent=2))

if __name__=='__main__':main()
