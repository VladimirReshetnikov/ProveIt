"""Fresh boundary239 guard check using audited symbolic rules, not old receipts."""
from pathlib import Path
import hashlib, importlib.util, json, sys, time
ROOT=Path(__file__).resolve().parent
B=ROOT.parent/'combine/zfc239-research-20261019'
sys.path.insert(0,str(B/'validation'))
import symbolic_runtime as s
if not __debug__ or sys.flags.optimize: raise RuntimeError('Enabled assertions required')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
path=B/'candidate239/zfc_boundary239_old.tm'
site_path=B/'candidate239/sites_logical.json'
table=s.r.table(path);sites=json.loads(site_path.read_text())
assert digest(path)=='d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719'
assert digest(site_path)=='7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
working={q for q,b in table}
assert len(working)==239 and len(table)==478
assert set(table)=={(q,b) for q in working for b in (0,1)}
assert {t for w,d,t in table.values()}-working=={254}
assert all(table[169,b][2]!=169 for b in (0,1))
assert 95 in working and 96 in working and 254 not in working
leaves=set();prefixes=set()
for pc,op,arg in sites:
    assert isinstance(pc,str) and 0<len(pc)<=64 and set(pc)<={'0','1'}
    assert pc not in leaves
    assert op in ('CI','CD','CB','CC','CH')
    if op=='CH': assert arg is None
    elif op in ('CI','CD'): assert type(arg) is int and 0<=arg<9
    else: assert type(arg) is int and arg>=1
    leaves.add(pc);prefixes.update(pc[:i] for i in range(len(pc)))
assert not leaves.intersection(prefixes)
assert all(p+b in leaves or p+b in prefixes for p in prefixes for b in ('0','1'))
assert len(leaves)==6455 and len(prefixes)==6454
q=95;h=0;ones=set();boot=[]
for tick in range(409691):
    read=int(h in ones)
    if q==169:
        if read: assert h+1 in ones, ('boot guard violation',tick,h)
        boot.append({'tick':tick,'head':h,'read':read,'right_neighbor':int(h+1 in ones)})
    w,d,q=table[q,read]
    if w:ones.add(h)
    else:ones.discard(h)
    h+=d
assert q==96 and h==-5
reference=json.loads((B/'candidate239/blank_prefix.json').read_text())
# Exact full endpoint checked against the independent mathematical frame as well.
want={v-5 for v in s.r.frame('',[3,0,0,0,3,0,0,0,0],[1]*167,117)}
assert ones==want and len(ones)==351
context={'stage':'block derivation'};events=[];all169=0;step=s.State.step

def guarded(self,tab,lemmas,clock,motion):
    global all169
    self.key()
    if self.q==169:
        all169+=1
        src=self.right if self.direction==1 else self.left
        assert src and src[0][0] in ('run','blank'), ('169 would be hidden by opaque/list step',self.key())
        if src[0][0]=='run' and src[0][1]==1:
            length=src[0][2]
            assert self.direction==1 and s.nonnegative(length) and length[0]>=2, ('failed guard',context,self.key())
            events.append({'context':dict(context),'right_one_run':length,'minimum':length[0]})
    return step(self,tab,lemmas,clock,motion)
s.State.step=guarded
started=time.monotonic();lemmas,blocks=s.prove_blocks(table)
for block in blocks:
    assert all(event[0]!='list' and event[1][0]!=169 and event[1][4]!=169 for event in block['trace'])
assert not any(key[0]==169 for key in lemmas)
print('Exact boot, complete source census, and non-hiding four block schemas passed.',flush=True)
cases=0;rules=0;min_duration=None
for index,site in enumerate(sites):
    for positive in ((False,True) if site[1]=='CD' else (False,)):
        context={'site_index':index,'site':site,'positive':positive}
        answer=s.case(table,lemmas,site,positive)
        cases+=1;rules+=answer['symbolic_steps'];min_duration=min(answer['duration'][0],min_duration) if min_duration is not None else answer['duration'][0]
        if cases%1000==0:print('Guarded',cases,'cases;',len(events),'positive169 events;',round(time.monotonic()-started,2),'seconds',flush=True)
assert cases==8386 and events
receipt={'status':'BOUNDARY239_UNBOUNDED_SELECTOR_GUARD_PASS','table_sha256':digest(path),'sites_sha256':digest(site_path),'checker_sha256':digest(Path(__file__)),'engine_sha256':digest(Path(s.__file__)),'helper_sha256':digest(Path(s.r.__file__)),'boot_steps':409691,'boot_endpoint':{'state':q,'head':h,'one_cells':len(ones),'logical':[3,0,0,0,3,0,0,0,0],'spares':[1]*167,'extra_gap':117},'boot169_events':boot,'cases':cases,'symbolic_rules':rules,'minimum_actual_duration':min_duration,'all169_symbolic_visits':all169,'positive169_events':events,'positive169_minimum':min(e['minimum'] for e in events),'list_schemas_cannot_hide169':True,'unary_rules_cannot_hide169':True,'blocks':blocks,'seconds':time.monotonic()-started,'scope':'Every state169/read1 during blank startup and every complete symbolic instruction family sees another1 immediately to its right. No arbitrary-tape guard or proof-assistant certification is claimed.'}
(ROOT/'boundary_guard.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ('blocks','positive169_events','boot169_events','boot_endpoint')},indent=2),flush=True)
