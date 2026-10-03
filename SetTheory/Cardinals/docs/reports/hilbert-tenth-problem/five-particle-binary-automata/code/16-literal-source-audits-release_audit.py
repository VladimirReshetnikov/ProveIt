#!/usr/bin/env python3
"""Independent release audit; no generator imports, no CA factors allocated.
Run: python release_audit.py [source-dir]. Uses a private replay copy only.
All audit checks remain active under python -O.
"""
import collections,copy,hashlib,importlib.util,itertools,json,pathlib,shutil,subprocess,sys,time
HERE=pathlib.Path(__file__).resolve().parent
SOURCE=pathlib.Path(sys.argv[1]).resolve() if len(sys.argv)>1 else HERE.parent/'source'
WORK=HERE/('optimized-replay' if sys.flags.optimize else 'normal-replay')
LOGS=WORK/'audit-logs'
def check(ok,msg):
    if not ok: raise RuntimeError(msg)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def nodup(ps):
    d={}
    for k,v in ps:check(k not in d,'duplicate JSON key');d[k]=v
    return d
def read(p):return json.loads(p.read_text(),object_pairs_hook=nodup)
def module(name,p):
    sp=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m
def reject(fn,*a,**kw):
    try:fn(*a,**kw)
    except (ValueError,TypeError):return
    raise RuntimeError('invalid call accepted')
if WORK.exists():shutil.rmtree(WORK)
shutil.copytree(SOURCE,WORK,ignore=shutil.ignore_patterns('__pycache__'))
LOGS.mkdir()
manifest={str(p.relative_to(SOURCE)):digest(p) for p in SOURCE.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
receipt={'status':'RUNNING','source_identifier':'bundled source tree identified by source_hashes','audit_script_sha256':digest(pathlib.Path(__file__)),'source_hashes':manifest,'optimized_audit':bool(sys.flags.optimize)}
s=read(WORK/'source.json'); p=read(WORK/'reversible2-primitives.json');h=read(WORK/'reversible5.json');n=read(WORK/'normalized3.json');v=read(WORK/'dependency/virtual3.json');tm=read(WORK/'dependency/tm_table.json');cert=read(WORK/'certificates.json')
check(digest(WORK/'source.json')=='38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a','source pin')
check(len(s['controls'])==122622 and len(s['branches'])==141561 and s['class_cut']==0,'source counts')
# Independent all-natural proof for this literal primitive alphabet via symbolic
# coordinate-class masks, computed directly from operation domains and images.
# Each class is {0} or all positive integers, not a bounded grid sample.
def masks(row):
    i=row['counter'];op=row['symbol'];d=(3,3);im=(3,3)
    if op=='Z':d=im=tuple(1 if j==i else 3 for j in range(2))
    elif op=='P':d=im=tuple(2 if j==i else 3 for j in range(2))
    elif op=='-':d=tuple(2 if j==i else 3 for j in range(2))
    elif op=='+':im=tuple(2 if j==i else 3 for j in range(2))
    else:check(op=='0','unknown primitive')
    return d,im
for key,index in [('source',0),('target',1)]:
    groups=collections.defaultdict(list)
    for e in p['rows']:groups[e[key]].append(masks(e)[index])
    for q,ms in groups.items():
        for x,y in itertools.combinations(ms,2):check(not all(a&b for a,b in zip(x,y)),key+' rectangle overlap '+q)
check(s['controls']==p['controls'] and s['controls'][0]=='START','control linkage')
for name in ('primitive3.json','normalized3.json','reversible5.json','reversible2-primitives.json'):
    x=read(WORK/name);check(not any(e['target']=='START' for e in x['rows']),name+' incoming start');check(not any(e['source']=='HALT' for e in x['rows']),name+' outgoing halt')
check(set(n['controls'])<set(h['controls'])<set(p['controls']),'boundary inclusion')
check(all(q.startswith('h') for q in set(h['controls'])-set(n['controls'])),'history interior names')
check(all(q.startswith(('p','r')) for q in set(p['controls'])-set(h['controls'])),'prime interior names')
check(v['tm_cuts']['J1']=='HALT' and 'HALT' not in v['rows'],'TM halt linkage')
check(set(tm)==set(v['tm_cuts']) and sum(t is None for t in tm.values())==1,'TM interface')
# Finite corroboration of independently derived TM-step clock and operation.
tm_cases=0
for state,tr in tm.items():
    if tr is None:continue
    w,mov,dest=tr;X=0 if mov=='L' else 1;Y=1-X
    for L,R in itertools.product(range(9),repeat=2):
        regs=[L,R,0];old=regs[:];Q,bit=divmod(old[X],2);want=old[:];want[X]=Q;want[Y]=2*old[Y]+w
        end=v['tm_cuts'][dest+str(bit)];q=v['tm_cuts'][state];clock=5*Q+bit+7*old[Y]+w+4
        for t in range(1,clock+1):
            op,i,*ds=v['rows'][q]
            if op=='ADD':regs[i]+=1;q=ds[0]
            elif regs[i]:regs[i]-=1;q=ds[0]
            else:q=ds[1]
            check(not (q=='HALT' and t<clock),'premature TM halt')
        check(q==end and regs==want,'TM operation/clock')
        tm_cases+=1
receipt['independent_tm_macro_cases']=tm_cases
# Exact class ledger from actual guards.
B=r=P=0
for e in s['branches']:
    g=e['guard'];check(g['op'] in ('true','eq','gt'),'unexpected guard')
    for a,b in itertools.product(range(2),repeat=2):
        c=(a,b);enabled=g['op']=='true' or (c[g['counter']]==0 if g['op']=='eq' else c[g['counter']]>0)
        if enabled:B+=1;r+=a+b;P+=int(e['delta']!=0)
receipt['class_expansion']={'B':B,'r':r,'P':P,'core_variables_per_H':B+2+r,'core_squares_per_H':4+2*B,'orthant_squares_per_H':5+2*B,'raw_slots_per_H':7*B+P+r+5}
check((B,r,P)==(350054,411291,199004),'class ledger')
# Compiler ledger independently spelled out from the audited factor indexing.
m=len(s['controls']);moving=sum(e['delta']!=0 for e in s['branches']);a=len(s['branches'])-moving;D=2*m+4*moving;S=2*D+2;Z=40*D+60
pair=4*moving;triple=8*moving*D+23*moving+m;context=2*moving+a
factors=pair+triple+context;radius=pair*(6*D+8)+triple*(24*D+32)+context*(Z+12*D+16)
check((factors,radius)==(269291358255,3292955588459274804),'CA count/radius')
receipt['compiler']={'m':m,'p':moving,'a':a,'D':D,'S':S,'Z':Z,'factors':factors,'radius':radius,'observer_length':3*D+3}
# Public loader and indexed checker API tests, including exact types and isolation.
loader=module('audit_loader',WORK/'loader.py');validator=module('audit_validator',WORK/'validate_source.py')
check(loader.from_tape('101','01')=={'control':'START','counter0':288,'counter1':0},'tape direction')
check(loader.from_tape('','')==loader.from_counters(0,0),'empty tape')
for A in range(1,22):
    data={'control':'START','counter0':A,'counter1':0};before=copy.deepcopy(data)
    if A%7==0 or A%11==0:reject(loader.five_particle_input,data)
    else:
        got=loader.five_particle_input(data);check(got==sorted([-Z-A,0,Z,S,S+1]) and len(set(got))==5,'particle geometry');got[0]=0;check(loader.five_particle_input(data)[0]==-Z-A,'returned coordinate mutation leak')
    check(data==before,'caller data mutated')
g=loader.target_ledger();g['Z']=0;g['alphabet'].append(2);check(loader.target_ledger()['Z']==Z and loader.target_ledger()['alphabet']==[0,1],'ledger mutation leak')
class BadInt(int):pass
class BadString(str):pass
class BadDict(dict):pass
for value in (True,False,-1,1.,'1',None,BadInt(1)):
    reject(loader.from_counters,value,0);reject(loader.from_counters,0,value);reject(loader.from_counters,0,0,T=value)
for co in (0,2,3,5,7,11,2310):reject(loader.from_counters,0,0,cofactor=co)
reject(loader.from_tape,BadString('01'),'');reject(loader.five_particle_input,BadDict(control='START',counter0=1,counter1=0));reject(loader.five_particle_input,loader.from_tape('',''),ledger={'Z':0,'S':0})
base={'schema':'reversible-two-counter-v1','controls':['START','MID','HALT'],'start':'START','halt':'HALT','class_cut':0,'branches':[]}
validator.validate(base)
for k in ('schema','start','halt'):
    bad=copy.deepcopy(base);bad[k]=BadString(bad[k]);reject(validator.validate,bad)
reject(validator.validate,{BadString(k):x for k,x in base.items()})
for key,value in [('class_cut',True),('controls',('START','HALT')),('branches',()),('extra',1)]:
    bad=copy.deepcopy(base);bad[key]=value;reject(validator.validate,bad)
e={'name':'e','source':'START','target':'MID','side':-1,'delta':1,'guard':{'op':'true'}}
for badrow in [dict(e,delta=True),dict(e,delta=-1),dict(e,source='HALT'),dict(e,target='START'),dict(e,guard={'op':'eq','counter':0,'value':0})]:
    bad=copy.deepcopy(base);bad['branches']=[badrow];reject(validator.validate,bad)
for second in [dict(e,name='f'),dict(e,name='f',source='MID')]:
    bad=copy.deepcopy(base);bad['branches']=[e,second];reject(validator.validate,bad)
reject(json.loads,'{"schema":1,"schema":2}',object_pairs_hook=validator.nodup)
# Derive complete physical prologue clocks from literal five-counter traversal.
out=collections.defaultdict(list)
for e in h['rows']:out[e['source']].append(e)
PR=(2,3,5,7,11);pred=[]
for L,R,T,C in [(0,0,0,1),(1,0,0,1),(0,1,0,1),(0,0,0,13),(0,0,1,1)]:
    q='START';regs=[L,R,T,0,0];steps=clock=0
    while q!=v['tm_cuts']['A0']:
        enabled=[e for e in out[q] if e['symbol'] in ('+','0') or (regs[e['counter']]==0 if e['symbol']=='Z' else regs[e['counter']]>0)]
        check(len(enabled)==1,'prologue enabledness');e=enabled[0];prime=PR[e['counter']];op=e['symbol'];N=C
        for pp,z in zip(PR,regs):N*=pp**z
        if op=='0':cost=1
        elif op=='+':cost=(prime+7)*N+3
        elif op=='-':check(N%prime==0,'division promise');cost=4*N+(prime+3)*(N//prime)+3
        else:cost=4*N+4*(N//prime)+3
        clock+=cost;regs[e['counter']]+={'+':1,'-':-1}.get(op,0);q=e['target'];steps+=1;check(steps<1000,'small prologue bound')
    pred.append({'input_LRT_cofactor':[L,R,T,C],'final5':regs,'five_counter_steps':steps,'predicted_two_counter_steps':clock})
check(pred==read(WORK/'prologue-predicted-clocks.json')['cases'],'prologue receipt mismatch')
receipt['prologue_predictions']=pred
# All bundled checkers in both optimization modes; never in producer directory.
scripts=['check_primary_table.py','verify_virtual3.py','validate_source.py','verify_affine.py','independent_audit.py','test_loader.py','test_concrete.py','class_expansion_ledger.py']
runs=[]
def execute(script,opt,label):
    proc=subprocess.run([sys.executable]+(['-O'] if opt else [])+[script],cwd=WORK,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
    (LOGS/(label+'.log')).write_bytes(proc.stdout);return proc
for script,opt in itertools.product(scripts,[False,True]):
    label=script[:-3]+('-O' if opt else '-normal');proc=execute(script,opt,label);check(proc.returncode==0,label+' failed');runs.append(label)
receipt['bundled_replays']=runs
# Full deterministic regeneration, with exact hash equality of every generated table.
generated=['primitive3.json','normalized3.json','reversible5.json','reversible2-primitives.json','source.json','certificates.json','build-stats.json']
before={f:digest(WORK/f) for f in generated}
proc=execute('build_source.py',False,'regeneration');check(proc.returncode==0,'regeneration failed');check(before=={f:digest(WORK/f) for f in generated},'regeneration changed literal bytes')
receipt['regeneration_exact_files']=generated
# Controlled mutation tests: each affected saved-table checker must fail in both
# modes. Restore exact original bytes before each next independent test.
mutations=[('source.json','class_expansion_ledger.py',lambda x:next(e for e in x['branches'] if e['guard']['op']=='gt')['guard'].update(op='unknown')),('source.json','independent_audit.py',lambda x:x['branches'][next(i for i,e in enumerate(x['branches']) if e['delta'])].update(delta=0)),('reversible2-primitives.json','verify_affine.py',lambda x:next(e for e in x['rows'] if e['symbol']=='+').update(symbol='0')),('dependency/tm_table.json','check_primary_table.py',lambda x:x['A0'].__setitem__(0,1)),('dependency/virtual3.json','verify_virtual3.py',lambda x:x['rows'][next(k for k,row in x['rows'].items() if row[0]=='ADD')].__setitem__(1,0)),('certificates.json','test_concrete.py',lambda x:next(c for c in x['prime'] if c['kind']=='+').update(prime=13))]
mutation_results=[]
for filename,script,change in mutations:
    file=WORK/filename;original=file.read_bytes();bad=read(file);change(bad);check(bad!=json.loads(original),'ineffective mutation');file.write_text(json.dumps(bad,indent=2)+'\n')
    try:
        for opt in (False,True):
            label='mutation-'+script[:-3]+('-O' if opt else '-normal');proc=execute(script,opt,label);check(proc.returncode!=0,label+' silently accepted');mutation_results.append(label)
    finally:file.write_bytes(original)
# Source pin detects byte-level edits before supplying geometry; dependency pin
# rejects tampered build input before generation.
f=WORK/'source.json';raw=f.read_bytes();f.write_bytes(raw+b' ')
try:reject(loader.target_ledger)
finally:f.write_bytes(raw)
f=WORK/'dependency/virtual3.json';raw=f.read_bytes();f.write_bytes(raw+b' ')
try:
    for opt in (False,True):check(execute('build_source.py',opt,'mutation-build-'+str(opt)).returncode!=0,'builder ignored dependency pin')
finally:f.write_bytes(raw)
receipt['saved_table_mutations_rejected']=mutation_results
receipt['api_domain_immutability_checks']='PASS (public input/return isolation, malformed objects, duplicate JSON keys, source/dependency pins)'
# Mandatory bundled dependency pins replace optional external-tree reads.
DEPENDENCY_PINS={'dependency/virtual3.json': '24c771db50dc621068e470227802c2710a4531ce2e7ad3703a5cdb6b0543bbcf', 'dependency/virtual3.txt': '72338fd033a31d61e261d6074e6524d35a8d56022f8bcece411efb764fb02b5a', 'dependency/tm_table.json': '0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a', 'dependency/UniversalTM15x2.tm.txt': 'ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae', 'compiler-reference/reversible_binary.py': 'f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f'}
for local,expected in DEPENDENCY_PINS.items():
    check(digest(WORK/local)==expected,'bundled dependency pin mismatch: '+local)
receipt['bundled_dependency_sha256_checks']=DEPENDENCY_PINS
receipt['status']='PASS';receipt['limits']=['No full physical universal run or complete physical prologue executed','No CA factor objects or truth table allocated','Universality of primary TM is inherited; this audit verifies byte identity and interfaces, not a new visual transcription','Mathematical invariants/ranks are reviewed proofs, not proof-assistant checked']
(HERE/('release-audit-optimized-receipt.json' if sys.flags.optimize else 'release-audit-receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ('source_hashes','prologue_predictions')},indent=2))
