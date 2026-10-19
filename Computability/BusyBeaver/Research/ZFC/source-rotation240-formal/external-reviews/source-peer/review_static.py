"""Independent static literal/source review. Does not import or execute Lean or delivered code."""
from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
D=Path('/tmp/zfc-source-rotation240'); O=Path(__file__).parent
S=D/'SourceRotation240.lean'; A=D/'Audit.lean'
P=Path('/tmp/zfc-routing245-lean/program/generated-v4/ProgramRouting245.lean')
L=Path('/tmp/zfc-intake-e5c2b3337e/zfc240-source-rotation-20261018/machines/sites_logical.json')
def desc(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
checks=[]
def ck(ok,why):
    assert ok,why
    checks.append(why)
text=P.read_text(); rows={}
for i,body in re.findall(r'private def row(\d{3}) : Row := (.+)',text):
    edges=re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?',body)
    ck(len(edges)==2,'two edges '+i)
    rows[int(i)]=tuple((k,int(v) if v else None) for k,v in edges)
ck(set(rows)==set(range(203)),'complete203 literal rows')
old=dict(rows);old[5]=(('decnz',6),('cont',2));old[6]=(('inc',0),('node',5))
new=dict(old);new[169]=(('inc',5),('node',5))
ck(old[169]==(('node',45),('inc',5)),'local old entry')
ck(old[45]==(('decnz',6),('node',44)),'local old test')
ck(old[44]==(('inc',5),('cont',2)),'local old transfer')
ck(new[5]==(('decnz',6),('cont',2)),'local new test')
ck(all(old[n]==new[n] for n in range(203) if n!=169),'all other rows identical')
s=S.read_text();a=A.read_text()
ck('if n = 169 then (.inc 5, .node 5)' in s,'single explicit override')
ck('Replacement oldDag newDag (fun _ => True) 169' in s,'unrestricted context admits shared children')
ck(re.findall(r'^set_option (.+)$',s,re.M)==['autoImplicit false'],'default proof limits')
Bset={int(x) for x in re.findall(r'n = (\d+)',s.split('private def B')[1].split('private def C')[0])}
cbody=s.split('private def C')[1].split('private theorem')[0]
C2={int(x) for x in re.findall(r'n = (\d+)',cbody.split('then 2')[0])}
C1={int(x) for x in re.findall(r'n = (\d+)',cbody.split('else if')[1].split('then 1')[0])}
B=lambda n:int(n in Bset)
C=lambda n:2 if n in C2 else int(n in C1)
for n,(l,r) in new.items():
    for side,e in enumerate((l,r)):
        k,v=e
        ck(k!='node' or v<203,'edge valid '+str((n,side)))
        ck(k not in ('brk','cont') or v>0,'positive escape '+str((n,side)))
        ck((v+1 if k=='node' else 0)<n+1,'height '+str((n,side)))
    b=lambda e:B(e[1]) if e[0]=='node' else 1 if e[0]=='decnz' else e[1] if e[0]=='brk' else 0
    c=lambda e:C(e[1]) if e[0]=='node' else e[1] if e[0]=='cont' else 0
    ck(b(l)<=B(n)+1 and b(r)<=B(n) and c(l)<=C(n) and c(r)<=C(n)+1,'escape bounds '+str(n))
ck(B(202)==C(202)==0 and 202<203 and 203<=204,'root bounds')
ops={'inc':'CI','decnz':'CD','brk':'CB','cont':'CC','halt':'CH'}
leaves=[]
def visit(e,p):
    k,v=e
    if k=='node':
        for bit,ch in enumerate(new[v]):visit(ch,p+str(bit))
    else:leaves.append([p,ops[k],v])
visit(('node',202),'')
delivered=json.loads(L.read_text())
ck(len(leaves)==6455,'6455 leaves')
for i,(x,y) in enumerate(zip(leaves,delivered)):
    ck(x==y,'exact leaf '+str(i))
ck(len(delivered)==len(leaves),'all delivered leaves consumed')
ck(sum(2 if k=='CD' else 1 for _,k,_ in leaves)==8386,'8386 guarded cases')
probes=re.findall(r'^#print axioms (\S+)',a,re.M)
ck(len(probes)==10 and all(p.startswith('SetTheory.BusyBeaver.ZFC.SourceRotation240.') for p in probes),'10 qualified probes')
ck(len(re.findall(r'^example\b',a,re.M))==13,'13 typed clients')
inputs=[S,A,P,L,D/'provider-plan.json',R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMEquiv.lean',Path('/tmp/zfc-rmdag-loop-rotation/RMDagLoopRotation.lean'),Path('/tmp/zfc-rmdag-context-substitution/RMDagContextSubstitution.lean'),R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SourceRotation244.lean']
record={'status':'INDEPENDENT_SOURCE_API_REVIEW_PASS','source':desc(S),'audit':desc(A),'reviewer_source':desc(Path(__file__)),'inputs':[desc(p) for p in inputs],'static_checks':len(checks),'findings':[], 'scope':['Full source/audit and generic loop/context APIs read.','Own literal parser independently checks all203 rows, finite WF inequalities, exact6455 leaves and8386 guards.','Local normal forms preserve the complete arbitrary natural register file; safe=True is sound because every non169 row is unchanged, including shared44/45.','Endpoint proves source-halting equivalence to ProgramRotation244 only. No binary runtime/startup/consistency/PA result.'], 'limits':['Source-only: no Lean elaboration, proof timing, guard execution or actual proof evidence review.','Default-depth feasibility of kernel decide remains for root actual compilation.','Provider plan read; this receipt is not a full selected-provider guard review.'], 'reviewer_role':'Independent of this new source/audit author; previously authored related source/proof guards and current intake prose.','executed_supplied_programs':False,'maintained_edits':False}
(O/'review.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'review':desc(O/'review.json')}))
