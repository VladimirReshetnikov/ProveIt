"""Untrusted canonical four-field -> three-field proof-tree compiler.
Uses the entry-reserved scope schedule. No compiler code is imported by a checker.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import ast,copy,hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
FOUR=ROOT/'code/checker.py'
THREE=[ROOT/'code/checker_tokens.py',ROOT/'code/checker_nodes.py']
POS=HERE/'fixtures/native_positives.json'
ENTRY=HERE/'fixtures/entry_capture.json'

def compile_certificate(doc):
    tree=ast.parse(FOUR.read_text())
    nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id in ('k','i') for t in n.targets)]
    ns={};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(FOUR),'exec'),ns)
    data=copy.deepcopy(doc);goal=data.pop();i=ns['i']
    def check(g,a):
        s,u,t,m=r=data.pop();node={'packet':r,'goal':a,'floor':ns['k']}
        aa=i(a);ns['k']-=1
        candidate=[[[s] if s else 1,u,t],i(t,r[:3],3) if s else u]
        if aa in (ns['k'],*g,candidate):
            node['three']=r[:3];node['terminal']=True;return node
        hypothesis=m*3
        if not hypothesis:
            a=i(*a,t,2);hypothesis=a
        node['major']=check(g,m)
        hypothesis=i(hypothesis,(m or len(a)==2==u) and ns['k'])
        target=i(t,u)
        matched=(m,a)==(r[:2] if s else [t]*3,target)
        selected=i(t,s) if matched else a
        next_goal=i(selected,[ns['k']])
        if matched:node['three']=r[:3];node['rule']='specialization'
        elif m:node['three']=[m,1,1];node['rule']='D_elimination'
        else:node['three']=[[],u,t];node['rule']='D_introduction'
        node['continuation']=check(g+[hypothesis],next_goal)
        return node
    root=check([[]],goal)
    assert not data, ('unexpected unused prefix',len(data))
    def execution(node):
        out=[node['three']]
        if not node.get('terminal'):
            out+=execution(node['major'])+execution(node['continuation'])
        return out
    return list(reversed(execution(root)))+[goal]

cases=[]
for old in json.loads(POS.read_text())['cases']:
    doc=compile_certificate(old['certificate'])
    cases.append({'name':old['name'],'certificate':doc,'expected':True})
    cases.append({'name':old['name']+'_false_zero_one','certificate':doc[:-1]+[[1,[1]]],'expected':False})
    cases.append({'name':old['name']+'_false_one_zero','certificate':doc[:-1]+[[[1],1]],'expected':False})
# Keep the original entry-schedule capture attack, with the administrative marker recoded.
capture=next(copy.deepcopy(c) for c in json.loads(ENTRY.read_text())['cases'] if c['name']=='future_witness_capture')
for packet in capture['certificate'][:-1]:
    if type(packet)is list and len(packet)==3 and type(packet[0])is int and packet[0]==0:packet[0]=[]
cases.append(capture)
base=cases[0]['certificate']
for j,value in enumerate([None,True,False,1.5,'',{},'unused']):cases.append({'name':'opaque_unused_'+str(j),'certificate':[value]+base,'expected':True})
(HERE/'fixtures/entry_three_fixtures.json').write_text(json.dumps({'cases':cases},indent=2)+'\n')

def run(job):
    path,case,opt=job
    p=subprocess.run([sys.executable]+(['-O'] if opt else [])+[str(path)],input=json.dumps(case['certificate'])+'\n',capture_output=True,text=True,timeout=15)
    accepted=p.returncode==0 and p.stdout=='ACCEPT\n'
    row={'profile':path.name,'case':case['name'],'optimized':opt,'expected':case['expected'],'accepted':accepted,'exit_code':p.returncode}
    if accepted!=case['expected']:row['stderr_tail']=p.stderr[-1000:]
    return row
with ThreadPoolExecutor(max_workers=6) as pool:rows=list(pool.map(run,[(p,c,o) for p in THREE for c in cases for o in (False,True)]))
failures=[r for r in rows if r['accepted']!=r['expected']]
receipt={'compiler':'tests/verify_profiles.py:compile_certificate','source_four':{'path':str(FOUR.relative_to(ROOT)),'sha256':hashlib.sha256(FOUR.read_bytes()).hexdigest()},'profiles':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in THREE},'native_positive_cases':14,'false_goal_cases':28,'original_entry_capture_case':1,'opaque_prefix_cases':7,'process_runs':len(rows),'unexpected_outcomes':len(failures),'failures':failures,'results':rows}
(ROOT/'evidence/entry_three_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='results'},indent=2))
assert not failures
