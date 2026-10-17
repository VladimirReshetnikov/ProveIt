#!/usr/bin/env python3
"""Independent local-window certificates for the mixed-read fusion family.

Uses the overapproximating blank-reachable window graph of audit_tm.py.
At BOTH changed parent states, each reachable window must have a common
mapped configuration after positive local steps on both machines. Every
other state is handled by a single identical mapped step. This yields a
sufficient condition for blank-halting equivalence, independently of the
register instruction interface. Failure is not a semantic counterexample.
"""
from pathlib import Path
from functools import lru_cache
import argparse
import collections
import hashlib
import itertools
import json
import sys
import time
import hybrid_fusion_search as h
import audit_tm as audit

def certify_fusion(machine, windows, keep, dead, fused, radius, bound,
                   original_trace=None, check_states=None):
    """Return the first failed obligation or positive local block witnesses.

    check_states is a test hook. Production calls MUST leave it None, which
    checks both parents. The negative control demonstrates why omitting the
    kept parent is unsound when its outgoing action has been changed.
    """
    rows=machine.rows; halt=machine.halt
    def mapped(e): return audit.Edge(e.write,e.move,keep if e.target==dead else e.target)
    def reduced_trace(pattern):
        q,head=keep,0; out=[]
        for _ in range(bound):
            if q==halt or not -radius<=head<=radius: break
            i=head+radius; bit=(pattern>>i)&1
            e=fused[bit] if q==keep else mapped(rows[q,bit])
            pattern=(pattern&~(1<<i))|(e.write<<i)
            head+=e.move; q=e.target
            out.append((q,head,pattern))
        return out
    if original_trace is None:
        original_trace=lambda q,p:audit.local_trace(machine,q,p,radius,bound)
    rec=dict(tested_windows=0); certificate=[]
    for old in (keep,dead) if check_states is None else check_states:
        for pattern in windows.get(old,[]):
            bit=(pattern>>radius)&1
            if mapped(rows[old,bit])==fused[bit]: continue
            rec['tested_windows']+=1; targets={}
            for i,(q,head,tape) in enumerate(original_trace(old,pattern),1):
                key=('halt',)if q==halt else(keep if q==dead else q,head,tape)
                targets.setdefault(key,i)
            for j,(q,head,tape) in enumerate(reduced_trace(pattern),1):
                key=('halt',)if q==halt else(q,head,tape)
                if key in targets:
                    certificate.append([old,pattern,targets[key],j]);break
            else:
                rec['outcome']='no_local_certificate';rec['first_unmatched']=[old,pattern]
                return rec
    rec['outcome']='certified_blank_halting_equivalent';rec['certificate']=certificate
    return rec

def self_tests():
    """Accepted fusion and a counterexample to omitting the kept parent."""
    E=audit.Edge
    # Both parents halt on every tape in one or two steps. The hybrid halts
    # immediately. Different final head/tape values must be allowed at halt.
    m=audit.Machine(0,4,{(0,0):E(0,1,4),(0,1):E(1,-1,2),
                         (1,0):E(0,-1,3),(1,1):E(1,1,4),
                         (2,0):E(0,1,4),(2,1):E(1,1,4),
                         (3,0):E(0,1,4),(3,1):E(1,1,4)})
    windows={0:list(range(8)),1:list(range(8))}
    fused=(m.rows[0,0],m.rows[1,1])
    positive=certify_fusion(m,windows,0,1,fused,1,4)
    assert positive['outcome']=='certified_blank_halting_equivalent'
    assert positive['tested_windows']==8 and len(positive['certificate'])==8
    assert all((i,j)==(2,1)for q,p,i,j in positive['certificate'])
    # Independently materialize the quotient and replay each explicit
    # witness through the separate audit_tm local interpreter.
    candidate=audit.Machine(0,4,{(q,b):E(e.write,e.move,0 if e.target==1 else e.target)
                              for(q,b),e in m.rows.items()if q!=1})
    candidate.rows[0,0],candidate.rows[0,1]=fused
    for q,p,i,j in positive['certificate']:
        original=audit.local_trace(m,q,p,1,i)[-1]
        reduced=audit.local_trace(candidate,0,p,1,j)[-1]
        assert original[0]==m.halt and reduced[0]==m.halt
    # The source scans an all-zero tape forever. The mutant halts on its
    # very first step. Checking only the deleted parent would accept it.
    bad=audit.Machine(0,2,{(0,0):E(0,1,0),(0,1):E(1,1,1),
                           (1,0):E(0,1,2),(1,1):E(1,1,0)})
    bw=audit.window_reachable(bad,2)
    bf=(E(0,1,2),E(1,1,0))
    incomplete=certify_fusion(bad,bw,0,1,bf,2,8,check_states=(1,))
    proper=certify_fusion(bad,bw,0,1,bf,2,8)
    assert incomplete['outcome']=='certified_blank_halting_equivalent'
    assert proper['outcome']=='no_local_certificate' and proper['first_unmatched'][0]==0
    assert bad.rows[0,0]==E(0,1,0) and bf[0].target==bad.halt
    return dict(accepted_hybrid_fusion=True,independent_positive_witness_replay=True,
                rejected_unsound_deleted_parent_only_check=True,
                counterexample_source='inductive zero-preserving right scan forever',
                counterexample_mutant='halts on first blank step')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius',type=int,default=6)
    ap.add_argument('--bound',type=int,default=128)
    ap.add_argument('--output',type=Path,default=h.HERE/'hybrid-window-results.json')
    args=ap.parse_args()
    assert args.radius>=0 and args.bound>0
    for file,pin in h.PINS.items(): assert hashlib.sha256((h.SRC/file).read_bytes()).hexdigest()==pin
    compact,compact_start=h.read_table(h.SRC/'zfc_253.tm')
    labels=h.assignment(h.SRC/'12-sorts-code-regenerate_253.py','OLD_LABELS')
    rows={(labels[int(q)],b):audit.Edge(w,1 if d=='R'else -1,labels[int(n)]) for(q,b),(w,d,n)in compact.items()}
    machine=audit.Machine(labels[int(compact_start)],254,rows)
    box=h.assignment(h.SRC/'20-complete-vendor-decoder255-verify.py','BOX_STATES')
    protected={(q,b)for q in box for b in(0,1)}-{(3,0)}
    states=machine.states; nonbox=[q for q in states if q not in box]
    pairs=list(itertools.combinations(nonbox,2))+[(3,q)for q in nonbox if q!=96]
    begun=time.monotonic()
    controls=self_tests()
    windows=audit.window_reachable(machine,args.radius)
    @lru_cache(maxsize=100000)
    def original_trace(q,p): return audit.local_trace(machine,q,p,args.radius,args.bound)
    report=dict(scope='Sufficient positive-length local-window certificates for hybrid state fusion; no minimality claim',
                public253_table_sha256=h.PINS['zfc_253.tm'],ProveIt_commit='6ec2e80dbbe45a99b7812fb5757977307959a51e',
                public253_commit='0d544f2a2e3c18f12278441a74b7879f31cbe856',
                radius=args.radius,maximum_steps_per_side=args.bound,abstract_configurations=sum(map(len,windows.values())),
                candidate_pairs=len(pairs),duplicates_or_pure=0,protected_rejected=0,candidates=[],safe_fusions=[],controls=controls,
                driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for a,b in pairs:
        keep,dead=(a,b)if b!=96 else(b,a)
        def mapped(e): return audit.Edge(e.write,e.move,keep if e.target==dead else e.target)
        pure0=tuple(mapped(rows[keep,s])for s in(0,1))
        pure1=tuple(mapped(rows[dead,s])for s in(0,1))
        seen=set()
        for d0,d1 in((keep,dead),(dead,keep)):
            fused=(mapped(rows[d0,0]),mapped(rows[d1,1]))
            if fused in(pure0,pure1)or fused in seen:
                report['duplicates_or_pure']+=1;continue
            seen.add(fused)
            if any((fused[s] if q==keep else mapped(rows[q,s]))!=rows[q,s] for q,s in protected):
                report['protected_rejected']+=1;continue
            rec=dict(keep=keep,dead=dead,read0_from=d0,read1_from=d1,
                     **certify_fusion(machine,windows,keep,dead,fused,args.radius,args.bound,original_trace))
            if rec['outcome']=='certified_blank_halting_equivalent':
                report['safe_fusions'].append(rec.copy())
                print('SAFE',rec,flush=True)
            report['candidates'].append(rec)
    report['outcome_counts']=dict(collections.Counter(c['outcome']for c in report['candidates']))
    report['total_windows_tested']=sum(c['tested_windows']for c in report['candidates'])
    report['elapsed_seconds']=time.monotonic()-begun
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()if k not in('candidates','safe_fusions')},indent=2))
    print('SAFE FUSIONS',len(report['safe_fusions']))

if __name__=='__main__': main()
