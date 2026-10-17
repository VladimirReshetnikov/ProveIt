#!/usr/bin/env python3
"""Complement to source04's bounded folds of the actual public253 table.

Reuses source04 program_sites/cases/executor and source09's protected-box
boundary. The underlying affine executor is Jeff's attributed design checker,
not a kernel proof. Mira-Cult designed the machine, mira-emmy reduced it to253,
and Wade supplied TMBuilder. No checksum manifest or source mutation is used.
"""
from pathlib import Path
import argparse, ast, collections, datetime, hashlib, json, platform, shutil, sys, tempfile, time
if not __debug__:
    raise SystemExit('Run without -O/-OO: this experiment requires assertions.')
sys.dont_write_bytecode=True
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[4])
parser.add_argument('--output',type=Path,help='complete JSON evidence; defaults to a new scratch directory')
parser.add_argument('--affine-fuel',type=int,default=1000)
parser.add_argument('--boot-limit',type=int,default=313000)
parser.add_argument('--extended-boot-limit',type=int,default=2000000)
args=parser.parse_args()
if min(args.affine_fuel,args.boot_limit,args.extended_boot_limit)<1:
    parser.error('fuel limits must be positive')
if args.extended_boot_limit<args.boot_limit:
    parser.error('extended boot limit must be at least the initial limit')
REPO=args.repo.resolve()
HOST=REPO/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
WORK=Path(tempfile.mkdtemp(prefix='zfc-public253-folds-'))
(WORK/'source04').mkdir()
for source,target in [('04-machine-engineering-context_search.py','context_search.py'),
                      ('04-machine-engineering-analyze_table.py','analyze_table.py')]:
    shutil.copyfile(HOST/'code'/source,WORK/'source04'/target)
sys.path.insert(0,str(WORK/'source04'))
import context_search as cs


def read_table(path):
    rows={}; start=None
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! start '): start=int(line.split()[-1])
        elif line and not line.startswith('#'):
            q,b,w,d,n=line.split();rows[str(q),int(b)]=(int(w),d,str(n))
    assert start is not None
    return rows,str(start)


def literal_assignment(path,name):
    tree=ast.parse(Path(path).read_text())
    return next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign)
                and any(isinstance(t,ast.Name) and t.id==name for t in n.targets))


class Tracking(dict):
    def __init__(self, rows): super().__init__(rows);self.used=set()
    def __getitem__(self,k): self.used.add(k);return super().__getitem__(k)


old_order=literal_assignment(HOST/'code/12-sorts-code-regenerate_253.py','OLD_LABELS')
public_table=HOST/'data/04-machine-machines-zfc_253.tm'
assert hashlib.sha256(public_table.read_bytes()).hexdigest()==    '84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95'
compact,start=read_table(public_table)
table={(str(old_order[int(q)]),b):(w,d,str(old_order[int(n)])) for(q,b),(w,d,n)in compact.items()}
start=str(old_order[int(start)])
baseline_table=REPO/'lib/jeff-busy-beaver-zfc254/ZF/m254/machine/zfc_254.tm'
assert hashlib.sha256(baseline_table.read_bytes()).hexdigest()==    'd655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb'
base254,_=read_table(baseline_table)
reconstructed={k:v for k,v in base254.items() if k[0]!='8'}
reconstructed.update({('3',0):(0,'L','48'),('5',0):(1,'R','97'),('5',1):(1,'R','64'),('49',1):(0,'R','5')})
assert table==reconstructed and start=='5'
assert len(table)==506 and {q for q,b in table}=={str(q)for q in range(254)if q!=8}
assert {n for w,d,n in table.values()}-{q for q,b in table}=={'254'}
box=literal_assignment(HOST/'code/20-complete-vendor-decoder255-verify.py','BOX_STATES')
protected={(str(q),b)for q in box for b in(0,1)}-{('3',0)}
assert len(protected)==55 and all(table[k]==base254[k] for k in protected)
ns=cs.executor(table,REPO/'lib/jeff-busy-beaver-zfc254/ZF/m254/tools/tm/symexec.py')
sites=cs.program_sites(REPO/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v')
cases=cs.cases(ns,sites)
assert len(sites)==6460 and len(cases)==8391 and ns['D0']==40


def check_case(current,i,fuel=None):
    fuel=args.affine_fuel if fuel is None else fuel
    path_index,path,op,r,branch,expected=cases[i]
    ns['T']=current
    try:
        result=ns['run']('96',[('b',1)],ns['tape_R'](path,0,()),branch,expected,fuel=fuel)
        if result[0]==('halt'if op=='CH'else'ok'):
            return {'pass':True,'abstract_steps':result[1]}
        return {'pass':False,'reason':'unexpected_status','result':list(result)}
    except(ns['Fail'],KeyError)as ex:
        return {'pass':False,'reason':type(ex).__name__,'message':str(ex)}


# Independent explicit interpretation of Boot253.bootTarget253.
physical=[0,2,0,0,0,0,5,0,0]
spares=[0,0,1,0,0,0,0,0,1]+[0]*149
values=physical+spares
assert len(values)==167
head_target=-17
ones_target={head_target-1,head_target+40}
pos=head_target+41
for v in values:
    pos+=1
    for j in range(v+1):ones_target.add(pos+j)
    pos+=v+1
assert len(ones_target)==178 and min(ones_target)==-18 and max(ones_target)==366


def blank_run(current,initial,limit, *,detect_small_cycles=True):
    q,h,ones,t=initial,0,set(),0
    max_ones=0
    seen={}
    while True:
        if q=='96' and h==head_target and ones==ones_target:
            return {'outcome':'exact_target','steps':t,'head':h,'state':q,'ones':len(ones),
                    'all_integer_tape_cells_equal':True}
        if q=='254':return {'outcome':'halt','steps':t,'head':h,'state':q,'ones':len(ones)}
        if t==limit:return {'outcome':'fuel_limit','steps':t,'head':h,'state':q,'ones':len(ones)}
        if detect_small_cycles and len(ones)<30:
            key=(q,tuple(sorted(x-h for x in ones)))
            if key in seen and max_ones<len(ones_target):
                pt,ph=seen[key]
                return {'outcome':'exact_translation_cycle_with_fewer_than_30_ones','steps':t,
                        'period':t-pt,'head_translation':h-ph,'head':h,'state':q,'ones':len(ones),
                        'max_ones_entire_cycle_prefix':max_ones,'target_excluded_by_ones_count':True}
            if len(seen)<100000:seen[key]=(t,h)
        w,d,q=current[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R'else -1;t+=1
        max_ones=max(max_ones,len(ones))


begin=time.monotonic()
baseline=[]; usage=collections.defaultdict(list)
for i in range(len(cases)):
    traced=Tracking(table);r=check_case(traced,i);assert r['pass'],(i,r)
    baseline.append(r)
    for q in {q for q,b in traced.used}:usage[q].append((r['abstract_steps'],i))
for group in usage.values():group.sort()
baseboot=blank_run(table,start,313000,detect_small_cycles=False)
assert baseboot['outcome']=='exact_target'and baseboot['steps']==312975,baseboot
result={'status':'running','scope':'bounded actual253 folds; attributed affine box contracts; not a kernel proof or global minimality result',
        'source04_reuse':['program_sites','cases','executor'],'source09_reuse':'conservative BOX_STATES/55 protected rows',
        'attribution':'Mira-Cult original machine; Jeff verification/affine design model; mira-emmy public253 reduction; Wade TMBuilder; report04/report09 search scaffolding',
        'table_source':'04-machine-machines-zfc_253.tm','public_pin':'0d544f2a2e3c18f12278441a74b7879f31cbe856',
        'table_sha256':hashlib.sha256(public_table.read_bytes()).hexdigest(),
        'functional_table_pins_checked':True,
        'table_identity_checked_against_four_edit_reconstruction':True,
        'baseline_affine_cases':len(cases),'baseline_affine_passed':len(baseline),'affine_case_fuel':args.affine_fuel,
        'candidate_boot_limit':args.boot_limit,'candidate_extended_boot_limit':args.extended_boot_limit,
        'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'python':platform.python_version(),
        'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'gap_lower_bound':40,'protected_pairs':sorted([list(k)for k in protected],key=lambda k:(int(k[0]),k[1])),
        'baseline_exact_boot':baseboot,'target_contract':{'old_state':96,'compact_state':33,'absolute_head':-17,'gap':40,'physical_primary_registers':physical,'spares':spares,'full_ones_absolute':sorted(ones_target)},
        'candidates':[],'affine_survivors':[],'exact_boot_survivors':[]}
out=args.output.resolve() if args.output else WORK/'results.json'
out.parent.mkdir(parents=True,exist_ok=True)
def save():
    result['elapsed_seconds']=time.monotonic()-begin
    out.write_text(json.dumps(result,indent=2)+'\n')
save()
print('BASELINE PASS8391 affine; exact boot312975; protected55',flush=True)
states={q for q,b in table}
for dead in('5','84'):
    for replacement in sorted(states-{dead},key=int):
        candidate={(q,b):(w,d,replacement if n==dead else n)for(q,b),(w,d,n)in table.items()if q!=dead}
        changed_rows=[list(k)for k in protected if candidate.get(k)!=table[k]]
        assert not changed_rows
        assert len(candidate)==504
        mappedstart=replacement if start==dead else start
        assert mappedstart in{q for q,b in candidate}
        assert all(n in states-{dead}|{'254'}for w,d,n in candidate.values())
        c={'dead_old':dead,'replacement_old':replacement,'start_old':start,'mapped_start_old':mappedstart,
           'working_states':252,'rows':504,'all55_protected_pairs_unchanged':True,
           'rewritten_incoming_rows':[list(k)for k,v in table.items()if k[0]!=dead and v[2]==dead],
           'baseline_affected_cases':len(usage[dead]),'affine_checked':0,'affine_passed':0}
        # Baseline cases not visiting dead have literally unchanged explicit
        # execution and unchanged box summaries. Survivors receive all8391 too.
        for steps,i in usage[dead]:
            r=check_case(candidate,i);c['affine_checked']+=1
            if not r['pass']:
                c['affine_outcome']='failed';c['first_failure']={'case':i,'site':list(cases[i][:-1]),**r};break
            c['affine_passed']+=1
        else:
            for i in range(len(cases)):
                r=check_case(candidate,i);c['affine_checked']+=1
                if not r['pass']:
                    c['affine_outcome']='failed_full_recheck';c['first_failure']={'case':i,'site':list(cases[i][:-1]),**r};break
                c['affine_passed']+=1
            else:
                c['affine_outcome']='all8391_passed';result['affine_survivors'].append([dead,replacement])
                print('AFFINE SURVIVOR',dead,'->',replacement,flush=True)
                c['blank_run']=blank_run(candidate,mappedstart,args.boot_limit)
                if c['blank_run']['outcome']=='fuel_limit' and args.extended_boot_limit>args.boot_limit:
                    # Redirected paths can change runtime;2M is the earlier
                    # public-bootstrap diagnostic cap, not a correctness bound.
                    c['blank_run_extra_reason']='Affine survivor can change startup duration; extend the finite diagnostic cap (default2M matches source04).'
                    c['blank_run_extended']=blank_run(candidate,mappedstart,args.extended_boot_limit)
                final=c.get('blank_run_extended',c['blank_run'])
                if final['outcome']=='exact_target':
                    result['exact_boot_survivors'].append([dead,replacement])
                    print('EXACT BOOT SURVIVOR',dead,'->',replacement,final,flush=True)
        result['candidates'].append(c)
    save()
    print('SOURCE DONE',dead,'candidates',len(result['candidates']),'affine_survivors',len(result['affine_survivors']),flush=True)
result['status']='completed'
assert len(result['candidates'])==504
result['outcomes']=dict(collections.Counter(c['affine_outcome']for c in result['candidates']))
result['blank_outcomes']=dict(collections.Counter(c.get('blank_run_extended',c.get('blank_run',{})).get('outcome','not_run_after_affine_failure')for c in result['candidates']))
result['no_global_minimality_claim']=True
result['finite_fuel_failure_is_not_impossibility']=True
save();print(json.dumps({k:result[k]for k in('status','outcomes','blank_outcomes','affine_survivors','exact_boot_survivors','elapsed_seconds')},indent=2),flush=True)

print('Evidence:',out,flush=True)
