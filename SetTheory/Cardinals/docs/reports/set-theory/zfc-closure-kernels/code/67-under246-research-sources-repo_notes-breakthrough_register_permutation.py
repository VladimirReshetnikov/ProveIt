#!/usr/bin/env python3
"""Bounded physical-register permutations of the public 253 runtime fold.

Check the three initial controls or all 36 permutations in the declared
family without network or Lean/Coq. This charges 252 actual
working states: labels are inherited, start is old 64 and halt is old 254.
It does not claim that any candidate initializes a consistency machine.

The copied source27 strict checker uses four unchanged register-box contracts;
all other tested rules are literal table transitions. Expected register effects
and decrement guards are conjugated, while PC arithmetic is kept exact.
The root-frame detector requires an empty PC and gap >=40, nine exact physical
registers, all remaining spare blocks, and blank exterior. It records rather
than verifies spare values/capacity; a positive needs that separate check. Failure to detect
such a frame within finite fuel is not a refutation of eventual initialization.
"""
import argparse
import datetime
import platform
import tempfile
import time
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
from types import SimpleNamespace


REPO=Path(__file__).resolve().parents[4]

SKIP=(60,44,31,56,38,40,28,64,69)
CORE={0,1,2,3,4,5,6,7,9,10,13,14,19,20,28,29,30,31,38,40,41,42,43,44,
      48,56,57,58,59,60,63,64,69,73,74,75,83,84,85,95,97,109,112,131}
PHYS=(6,7,0,2,1,8,4,3,5)
BOX_STATES={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
BOX_PAIRS={(str(q),b) for q in BOX_STATES for b in (0,1)}-{('3',0)}

def prepare(repo, work):
    global strict, T, sites, safe_classifier
    host=repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
    base=repo/'lib/jeff-busy-beaver-zfc254/ZF/m254'
    inputs=[('strict_affine.py',host/'code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'),
            ('zfc_254.tm',base/'machine/zfc_254.tm'),('Prog254.v',base/'coq/tm/Prog254.v')]
    records=[]
    for name,source in inputs:
        data=source.read_bytes();(work/name).write_bytes(data)
        records.append({'path':str(source.relative_to(repo)),'bytes':len(data),
                        'sha256':hashlib.sha256(data).hexdigest()})
    # strict.run does not use cost_search; that import belongs to its unused CLI.
    sys.modules['cost_search']=SimpleNamespace()
    spec=importlib.util.spec_from_file_location('strict_affine',work/'strict_affine.py')
    strict=importlib.util.module_from_spec(spec);spec.loader.exec_module(strict)
    T={}
    for line in (work/'zfc_254.tm').read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,t=line.split();T[q,int(b)]=(int(w),d,t)
    original=T.copy()
    T={k:v for k,v in T.items() if k[0]!='8'}
    T.update({('3',0):(0,'L','48'),('5',0):(1,'R','97'),('5',1):(1,'R','64'),('49',1):(0,'R','5')})
    T={k:(w,d,'64' if t=='5' else t) for k,(w,d,t) in T.items() if k[0]!='5'}
    assert len(T)==504
    assert len(BOX_PAIRS)==55
    assert all(T[p]==original[p] for p in BOX_PAIRS)
    assert all(original[p][2]!='5' for p in BOX_PAIRS)
    text=(work/'Prog254.v').read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',text)
    assert len(nodes)==6459
    sites=[]
    def visit(n,path):
        for b,e in enumerate(nodes[n]):
            p=path+str(b);kind,*arg=e.split()
            if kind=='CN':visit(int(arg[0]),p)
            else:
                r=int(arg[0]) if arg else None
                sites.append((p,kind,PHYS[r] if kind in ('CI','CD') else r))
    visit(0,'');assert len(sites)==6460
    safe_classifier=None
    safe_path=repo/'Computability/BusyBeaver/Research/ZFC/safe_seed254.py'
    if safe_path.exists():
        data=safe_path.read_bytes();(work/'safe_seed254.py').write_bytes(data)
        records.append({'path':str(safe_path.relative_to(repo)),'bytes':len(data),
                        'sha256':hashlib.sha256(data).hexdigest()})
        ss=importlib.util.spec_from_file_location('permutation_safe_seed',work/'safe_seed254.py')
        sm=importlib.util.module_from_spec(ss);ss.loader.exec_module(sm)
        safe_classifier=sm.state
    return records

def inc(p):
    if '0' not in p:return None
    return p[:p.rindex('0')]+'1'
def strip(p,bit,k):
    while k and p:
        k-=p[-1]==bit;p=p[:-1]
    return p

def certify(table,perm):
    passed=0;minimum=1000000
    for p,op,r in sites:
        for zero in ((True,False) if op=='CD' else (None,)):
            physical=perm[r] if op in ('CI','CD') else r
            branch=(physical,zero) if op=='CD' else None
            if op=='CI' or op=='CD' and not zero:succ=inc(p)
            elif op=='CD':succ=inc(strip(p,'0',1))
            elif op=='CB':succ=inc(strip(p,'0',r))
            elif op=='CC':succ=strip(p,'1',r)
            else:succ=''
            effect=('inc',physical) if op=='CI' else ('dec',physical) if op=='CD' and not zero else None
            right=([('r',0,1,41),('b',1),('box',('plain',effect))] if succ is None else
                   [('b',int(b)) for b in succ]+[('r',0,1,40-len(succ)),('b',1),('box',('plain',effect))])
            try:
                rules,literal=strict.run(table,p,branch,strict.canon([('b',1)],right),halt=op=='CH',fuel=1000)
                assert literal>0;minimum=min(minimum,literal);passed+=1
            except (AssertionError,KeyError) as exc:
                return {'passed':False,'cases_passed':passed,'failure':{'path':p,'operation':op,'old_physical':r,'new_physical':physical,'zero':zero,'message':str(exc)}}
    assert passed==8391
    return {'passed':True,'cases_passed':passed,'minimum_literal_rules':minimum}

def parse_root(q,h,ones,perm):
    if q!='96' or h-1 not in ones or min(ones)!=h-1:return None
    positive=sorted(x for x in ones if x>=h)
    if not positive:return None
    gap=positive[0]-h
    if gap<40:return None
    # Empty/root PC: the first one after the marker is the distant header.
    high=max(ones);cursor=h+gap+1;values=[]
    while cursor<=high:
        if cursor in ones:return None
        cursor+=1;v=0
        while cursor in ones:v+=1;cursor+=1
        if not v:return None
        values.append(v-1)
    if len(values)<9:return None
    logical=[values[perm[PHYS[r]]] for r in range(9)]
    return {'head':h,'gap':gap,'physical_primary':values[:9],
            'logical_primary':logical,'spares':values[9:],
            'whole_one_positions':sorted(ones),'all_other_cells_zero':True,
            'safe_three_formula_fields_zero':logical[1]==logical[2]==logical[5]==0,
            'safe_certificate':None if safe_classifier is None else safe_classifier(logical)}

def boot(table,perm,limit=1000000):
    """Literal blank run; root test is sufficient, deliberately not necessary."""
    q='64';h=0;ones=set();checkpoints=[];roots=[]
    for step in range(limit+1):
        frame=parse_root(q,h,ones,perm)
        if frame:
            frame['steps']=step;roots.append(frame)
            if (frame['safe_certificate'] is not None if safe_classifier is not None
                    else frame['safe_three_formula_fields_zero']):
                return {'outcome':'structural_root_frame_sufficient_Safe','frame':frame,'checkpoints':checkpoints}
        if step in (312935,312975,999186,1000000,10000000):
            checkpoints.append({'steps':step,'state':q,'head':h,'one_count':len(ones)})
        if q=='254':return {'outcome':'halt','steps':step,'checkpoints':checkpoints,'roots':roots}
        if step==limit:return {'outcome':'fuel_limit','steps':step,'checkpoints':checkpoints,'roots':roots}
        w,d,q=table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1

def encoded(table):
    return ('#! start 64\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(table.items(),key=lambda x:(int(x[0][0]),x[0][1])))).encode()

def family(selection):
    # Physical 7/8 remain top/cache. Physical 0 is the formula stack W.
    names={1:'D',2:'A',3:'Y',4:'X',5:'L',6:'N',7:'T',8:'H'}
    if selection=='controls3':
        pairs=[4,5,6]
    elif selection=='remaining28':
        pairs=[7,8]
    else:
        pairs=range(1,7)
    for other in pairs:
        perm=list(range(9));perm[0],perm[other]=other,0
        yield 'W_'+names[other],perm
    if selection in ('all36','remaining28'):
        bound=7 if selection=='all36' else 9
        for a in range(1,bound):
            for b in range(1,bound):
                if a==b or (selection=='remaining28' and a<7 and b<7):continue
                perm=list(range(9));perm[0],perm[a],perm[b]=a,b,0
                yield 'W_'+names[a]+'_'+names[b],perm


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,default=REPO)
    parser.add_argument('--scratch',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--family',choices=['controls3','all36','remaining28'],default='all36')
    parser.add_argument('--blank-limit',type=int,default=1000000)
    parser.add_argument('--extend-controls',type=int,default=0,
                        help='Optional second literal blank bound for W_X/W_N only')
    args=parser.parse_args()
    if not __debug__:parser.error('Assertions must remain enabled')
    if args.blank_limit<312935:parser.error('Blank limit must be at least312935')
    repo=args.repo.resolve()
    work=(args.scratch.resolve() if args.scratch else Path(tempfile.mkdtemp(prefix='zfc-breakthrough-permutation-')))
    if work==repo or repo in work.parents or work==Path('/'):
        parser.error('Scratch must be outside the repository and not filesystem root')
    work.mkdir(parents=True,exist_ok=True)
    begun=time.monotonic()
    source_inputs=prepare(repo,work)
    result={'scope':'Bounded register-conjugation diagnostic; no kernel, runtime simulation, consistency calibration or eventual-initialization claim.',
            'source_attribution':'Mira-Cult/Jeff/Wade original254; mira-emmy public253 PR20; source27 strict affine port.',
            'contract_scope':'All8391 affine cases are conditional on4 attributed Box contracts. Their55 source pairs are literally unchanged from original254 throughpublic253 andfold252; none isstate5or targets5. This Python driver doesnot reprove thosecontracts.',
            'source_pins':{'upstream':'297ab8df7e5de329605c3875b4934643b371a5e3',
                           'public253':'0d544f2a2e3c18f12278441a74b7879f31cbe856'},
            'input_files':source_inputs,'command':[sys.executable,*sys.argv],
            'python':platform.python_version(),'utc_started':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'scratch':str(work),'family':args.family,'Safe_classifier_available':safe_classifier is not None,'blank_limit':args.blank_limit,
            'frame_detector_scope':'Sufficient empty-PC/gap>=40 structural frame. Records all spares, but does not validate the runtime spare capacity/value contract. The sufficient Safe grammar is used when available, retaining the older zero-only flag; complete initializer validity requires a separate proof.',
            'state_convention':{'working_states':252,'rows':504,'start_label':64,'halt_label':254,'labels_not_canonical':True},
            'baseline':certify(T,list(range(9))),'candidates':[],'status':'running'}
    assert result['baseline']['passed']
    print('BASELINE 8391 PASS',flush=True)
    def save():
        result['elapsed_seconds']=time.monotonic()-begun
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    save()
    for name,perm in family(args.family):
        start=time.monotonic()
        mapping={str(SKIP[i]):str(SKIP[perm[i]]) for i in range(9)}
        candidate={key:(w,d,mapping.get(t,t) if int(key[0]) not in CORE else t)
                   for key,(w,d,t) in T.items()}
        changed=[{'state':q,'read':b,'before':list(T[q,b]),'after':list(v)}
                 for (q,b),v in candidate.items() if v!=T[q,b]]
        assert {q for q,_ in candidate}=={q for q,_ in T}
        assert all(candidate[k]==T[k] for k in T if int(k[0]) in CORE)
        data=encoded(candidate);table_path=work/(name+'.tm');table_path.write_bytes(data)
        record={'name':name,'physical_permutation':perm,'changed_rows':changed,
                'table_path':str(table_path),'bytes':len(data),
                'sha256':hashlib.sha256(data).hexdigest(),'affine':certify(candidate,perm)}
        if record['affine']['passed']:
            record['boot']=boot(candidate,perm,args.blank_limit)
            if (name in ('W_X','W_N') and args.extend_controls>args.blank_limit
                    and record['boot']['outcome']=='fuel_limit'):
                record['extended_boot']=boot(candidate,perm,args.extend_controls)
        record['elapsed_seconds']=time.monotonic()-start
        result['candidates'].append(record);save()
        print(name,'affine',record['affine']['passed'],
              'boot',record.get('boot',{}).get('outcome'),
              record.get('boot',{}).get('steps'),
              'seconds',round(record['elapsed_seconds'],3),flush=True)
    result['status']='complete';save()
    print('Evidence',args.output,flush=True)

if __name__=='__main__':main()

