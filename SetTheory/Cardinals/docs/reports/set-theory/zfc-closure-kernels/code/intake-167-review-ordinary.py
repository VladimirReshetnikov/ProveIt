#!/usr/bin/env python3
"""Own read-only literal/CFG comparison; imports no delivered code and runs no TM."""
from pathlib import Path
import ast, hashlib, json, re

ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
B=Path('/tmp/zfc244-d91a27b462-inspection/zfc244-loop-rotation-20261018/zfc244-loop-rotation-20261018')
OUT=Path(__file__).resolve().parent
count=0
def check(value):
    global count
    assert value
    count+=1
def desc(p):
    p=Path(p)
    return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def table(p):
    rows={}
    lines=Path(p).read_text().splitlines()
    check(lines[0].startswith('#! start '))
    start=int(lines[0].split()[-1])
    for line in lines[1:]:
        if not line.strip() or line.startswith('#'): continue
        q,b,w,d,t=line.split(); key=(int(q),int(b))
        check(key not in rows and int(b) in (0,1) and int(w) in (0,1) and d in ('L','R'))
        rows[key]=(int(w),d,int(t))
    return start,rows
def complete(t,n):
    states={q for q,b in t}
    check(len(states)==n and len(t)==2*n)
    check(set(t)=={(q,b) for q in states for b in (0,1)})
    check({v[2] for v in t.values()}-states=={254})
def incoming(t,q): return {k:v for k,v in t.items() if v[2]==q}
def patch(t,edits,deleted):
    return {k:edits.get(k,v) for k,v in t.items() if k[0] not in deleted}

oldp=B/'reference/baseline245/certificate/machine_old.tm'
rotp=B/'machine/machine_old.tm'
maintp=ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-routing245/zfc_routing245_old.tm'
compp=ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-compensated244/zfc_compensated244_old.tm'
start,old=table(oldp); rs,rot=table(rotp); cs,comp=table(compp)
check(start==rs==cs==95)
check(oldp.read_bytes()==maintp.read_bytes())
complete(old,245);complete(rot,244);complete(comp,244)
rotation={(12,0):(0,'R',18),(12,1):(1,'R',17),(17,1):(0,'L',20)}
compensation={(92,1):(1,'R',66),(104,1):(1,'R',92),(106,1):(1,'R',92),(167,1):(1,'L',151)}
check(patch(old,rotation,{26})==rot)
check(patch(old,compensation,{122})==comp)
check(not (rotation.keys() & compensation.keys()))
both=patch(rot,compensation,{122})
check(both==patch(comp,rotation,{26}))
complete(both,243)
check({q for q,b in old}-{q for q,b in both}=={26,122})
check(len([k for k in both if both[k]!=old[k]])==7)
rn=json.loads((B/'machine/renumbering.json').read_text())
mapping={int(k):v for k,v in rn['old_to_canonical'].items()}
_,canonical=table(B/'machine/machine.tm')
check(canonical=={(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in rot.items()})
check(mapping[95]==0 and mapping[96]==87 and mapping[254]==244)

blocks=Path('/tmp/zfc244-compensated-lean/blocks/Compensated244Blocks.lean')
refs={(int(q),int(b=='true')) for q,b in re.findall(r'foldRowRouting245_old(\d+)_(true|false)',blocks.read_text())}
newrefs={(int(q),int(b=='true')) for q,b in re.findall(r'foldRowCompensated244_old(\d+)_(true|false)',blocks.read_text())}
for key in refs: check(old[key]==rot[key])
for key in newrefs: check(comp[key]==both[key])
protected=[68,81,167,92,122]
for q in protected: check(incoming(old,q)==incoming(rot,q))
for q in (68,167):
    check(all(v==(1,'R',q) for v in incoming(rot,q).values()))
check(set(incoming(rot,81))=={(68,1),(123,0)})
check(rot[68,1]==(1,'R',81) and rot[123,0]==(0,'R',81))
check(set(incoming(rot,122))=={(104,1),(106,1)})
check(set(incoming(rot,92))=={(81,1),(167,1)})
for key,value in both.items():
    q,b=key
    if q!=92 and key not in {(81,1),(104,1),(106,1),(167,1)}:
        check(value==rot[key] and value[2] not in {92,122})

ositesp=B/'reference/baseline245/certificate/sites_logical.json'
nsitesp=B/'machine/sites_logical.json'
osites=json.loads(ositesp.read_text()); nsites=json.loads(nsitesp.read_text())
check(len(osites)==6460 and len(nsites)==6459)
check(osites[6:10]==[['01100','CD',6],['011010','CI',0],['011011','CC',2],['0111','CI',0]])
check(nsites==osites[:6]+[['0110','CI',0],['01110','CD',6],['01111','CC',2]]+osites[10:])
def cfg(sites):
    leaves={p:i for i,(p,o,r) in enumerate(sites)}
    check(len(leaves)==len(sites) and list(leaves)==sorted(leaves))
    prefixes={p[:i] for p in leaves for i in range(len(p))}
    check(not (prefixes & leaves.keys()))
    check(all(p+'0' in prefixes|leaves.keys() and p+'1' in prefixes|leaves.keys() for p in prefixes))
    def locate(p):
        # Strip consumed trailing zero padding, or descend on implicit zero input.
        cur=''
        for k in range(max(map(len,leaves))+1):
            if cur in leaves:
                check(set(p[k:]) <= {'0'})
                return leaves[cur]
            cur+=p[k] if k<len(p) else '0'
        raise AssertionError('missing leaf')
    def inc(p):
        i=p.rfind('0')
        return p[:i]+'1'+'0'*(len(p)-i-1) if i>=0 else '0'*len(p)
    def jump(p,bit,n):
        cuts=[i for i,c in enumerate(p) if c==bit]
        stem=p[:cuts[-n]] if len(cuts)>=n else ''
        return inc(stem) if bit=='0' else stem
    edges=[]
    for p,o,r in sites:
        if o=='CI': e={'inc':inc(p)}
        elif o=='CD': e={'zero':jump(p,'0',1),'positive':inc(p)}
        elif o=='CB': e={'control':jump(p,'0',r)}
        elif o=='CC': e={'control':jump(p,'1',r)}
        else: check(o=='CH' and r is None); e={}
        edges.append({k:locate(v) for k,v in e.items()})
    return edges,locate('')
oe,oi=cfg(osites);ne,ni=cfg(nsites)
mp={i:i if i<6 else i-1 for i in range(6460) if i<6 or i>=10};mp[6]=6
edges=0;ins=[]
for i,j in mp.items():
    if i==6:continue
    check(osites[i][1:]==nsites[j][1:])
    check(oe[i].keys()==ne[j].keys())
    for branch,tgt in oe[i].items():
        check(tgt in mp and mp[tgt]==ne[j][branch]);edges+=1
        if tgt==6:ins.append([i,branch])
check(edges==8385 and ins==[[2,'zero']] and mp[oi]==ni)
check(oe[6:10]==[{'zero':9,'positive':7},{'inc':8},{'control':6},{'inc':10}])
check(ne[6:9]==[{'inc':7},{'zero':9,'positive':8},{'control':6}])
check([i for i,s in enumerate(osites) if s[1]=='CH']==[6324])
check([i for i,s in enumerate(nsites) if s[1]=='CH']==[6323])
check(sum(2 if o=='CD' else 1 for p,o,r in nsites)==8390)

syntax=[]
for p in sorted((B/'code').glob('*.py')):
    try: ast.parse(p.read_text()); result={'status':'PARSES'}
    except SyntaxError as e: result={'status':'SYNTAX_ERROR','kind':type(e).__name__,'line':e.lineno,'message':e.msg}
    syntax.append({'file':desc(p),**result})
check([x['file']['path'].split('/')[-1] for x in syntax if x['status']!='PARSES']==['check_whole_frame_candidate.py'])

result={'status':'SOURCE_METADATA_REVIEW_COMPLETE','scope':'Own static literal and finite CFG comparisons only; no supplied checker, simulator, compiler or certificate replay.',
 'reviewer_source':desc(__file__),'checks':count,
 'inputs':[desc(p) for p in [oldp,maintp,rotp,compp,ositesp,nsitesp,blocks,B/'machine/machine.tm',B/'machine/renumbering.json']],
 'rotation_edits':[[*k,*v] for k,v in sorted(rotation.items())],
 'compensation_edits':[[*k,*v] for k,v in sorted(compensation.items())],
 'combined_static_census':{'states':243,'rows':486,'deleted_old_labels':[26,122],'changed_retained_rows':7,'unchanged_retained_rows':479,'start_old':95,'halt_old':254},
 'local_block_row_dependencies_old':[list(k) for k in sorted(refs)],'local_block_row_dependencies_new':[list(k) for k in sorted(newrefs)],
 'protected_incoming_rows':{str(q):[[*k,*v] for k,v in sorted(incoming(rot,q).items())] for q in protected},
 'source_context':{'old_leaves':6460,'new_leaves':6459,'new_guard_cases':8390,'outside_edges':edges,'external_entries':ins,'halt_sites':[6324,6323]},
 'primary_script_syntax':syntax,
 'claims_not_made':['No fresh supplied replay','No combined243 blank step count','No kernel theorem for rotation244 or combined243','No internal PA endpoint']}
(OUT/'static-comparison.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'checks':count,'output':desc(OUT/'static-comparison.json')},indent=2))
