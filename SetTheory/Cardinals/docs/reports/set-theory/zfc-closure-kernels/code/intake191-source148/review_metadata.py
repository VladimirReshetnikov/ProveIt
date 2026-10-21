#!/usr/bin/env python3
"""Own literal/receipt audit. Imports no delivered code and executes no machine."""
from pathlib import Path
import hashlib,json,collections,subprocess
A=Path('/tmp/zfc-intake191/K217_Search_Round_2026-10-20/K217_Search_Round_2026-10-20')
D=Path(__file__).resolve().parent; C=D/'replay1/copy';R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
def ck(name,v):
    assert v,name
    checks.append(name)
def table(p):
    d={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,m,t=line.split();k=(int(q),int(b));ck('unique row '+str(k),k not in d)
        d[k]=(int(w),1 if m=='R' else -1,int(t))
    states={q for q,b in d};ck(str(p)+' rows complete',len(d)==2*len(states));ck(str(p)+' targets',all(x[2] in states|{254} for x in d.values()))
    return d
base=R/'Computability/BusyBeaver/Research/ZFC/candidate-k218'
ck('accepted primary table literal', (A/'latest218_baseline/candidate-k218/k218.native.tm').read_bytes()==(base/'k218.native.tm').read_bytes())
ck('accepted primary source literal',(A/'latest218_baseline/candidate-k218/sites218.json').read_bytes()==(base/'sites218.json').read_bytes())
T=table(base/'k218.native.tm'); U=table(C/'research217_encoding/crossover30_primary/raw218.native.tm');V=table(C/'research217_bootstrap/crossover30/initialized217.native.tm')
expected={(193,0):(0,1,196),(193,1):(1,1,195),(195,0):(0,1,197),(195,1):(1,1,196)}
ck('exact four crossover edits',{k:a for k,a in U.items() if T[k]!=a}==expected)
fold={(87,0):(0,1,88),(88,0):(0,-1,51),(51,0):(0,1,122)}
ck('exact delete301 and three edits',V=={k:fold.get(k,a)for k,a in U.items()if k[0]!=301})
ck('state counts',[len(T)//2,len(U)//2,len(V)//2]==[218,218,217])
def source(p):
    rows=json.loads(p.read_text());by={x[0]:(x[1],x[2])for x in rows};ck('unique source addresses '+str(p),len(by)==len(rows))
    intervals={}
    for i,(path,op,arg)in enumerate(rows):
        for n in range(len(path)+1):
            v=intervals.setdefault(path[:n],[i,i+1]);v[1]=i+1
    trees=set()
    def tree(path):
        if path in by:t=by[path]
        else:t=(tree(path+'0'),tree(path+'1'))
        trees.add(t);return t
    tree('');edges=[]
    for i,(path,op,arg) in enumerate(rows):
        def jump(bit,k):
            inds=[j for j,v in enumerate(path) if v==bit]
            if len(inds)<k:return 0
            pre=path[:inds[-k]];return intervals[pre][0 if bit=='1' else 1]%len(rows)
        targets=[] if op=='CH' else [jump('1',arg)] if op=='CC' else [jump('0',arg)] if op=='CB' else [jump('0',1),(i+1)%len(rows)]if op=='CD' else [(i+1)%len(rows)]
        edges.append(targets)
    return rows,edges,len(trees)
a,ae,an=source(base/'sites218.json');b,be,bn=source(C/'research217_encoding/crossover30_primary/sites.json')
ck('whole primitive word',[r[1:]for r in a]==[r[1:]for r in b]);ck('all ordinal successors',ae==be);ck('exact source size',len(a)==4744 and an==bn==205)
changed=[i for i,(x,y)in enumerate(zip(a,b))if x!=y];ck('only advertised interval',changed and min(changed)>=4567 and max(changed)<4597)
ck('problem CC2 remains',[a[4569][1:],b[4569][1:]]==[['CC',2],['CC',2]] and a[4569][0].endswith('01') and b[4569][0].endswith('01'))
mp={int(k):v for k,v in json.loads((C/'research218_encoding/NATIVE_TO_LEGACY.json').read_text()).items()};needed={q for q,b in V}|{254};ck('runtime mapping covers states',needed<=mp.keys());ck('runtime mapping injective',len({mp[k]for k in needed})==len(needed))
pins=['README.md','report.tex','REPRODUCE.md','research217_native_basis_review/NATIVE_CALIBRATION.md','research217_native_basis_review/THREE_FIELD_ENUMERATOR_BRIDGE.md','research217_codec_pairing/CODEC_ISOMORPHISM.md','research217_pairing_macros/MACRO_CONTRACTS.md','research218_round2_rho8/MIXED_ORIENTATION_UNION_OBSTRUCTION.md','research218_round2_rho8/ALL_MEMBERSHIP_FOURTH_OBSTRUCTION.md','research217_mixed_tag_basis/MIXED_R_I_OBSTRUCTION.md','research217_encoding/AX_ROW_CONTRACT_PROOF.md','research217_bootstrap/CD5_SOURCE_FINDINGS.md','research217_bootstrap/EQUALITY_PRODUCER_FINDINGS.md']
result={'status':'OWN_LITERAL_METADATA_PASS','checks':len(checks),'reviewer':'drop_contract','scope':'Own inert parser; not a second machine replay or proof-assistant verification. Source/proof full-read scope described separately.','source_metrics':{'leaves':len(a),'ordinal_edges':sum(map(len,ae)),'baseline_dag':an,'crossover_dag':bn,'changed_addresses':changed,'site4569_baseline':a[4569],'site4569_crossover':b[4569]},'tables':{str(p.relative_to(C)):H(p)for p in [C/'research217_encoding/crossover30_primary/raw218.native.tm',C/'research217_bootstrap/crossover30/initialized217.native.tm']},'reviewed_document_pins':{p:H(A/p)for p in pins},'current_repository_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()}
(D/'literal-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in('reviewed_document_pins','source_metrics')},indent=2))
