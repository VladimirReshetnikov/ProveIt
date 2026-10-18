#!/usr/bin/env python3
"""Own static syntax/DAG/provider parser. No instruction or machine run is evaluated."""
from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
BASE=Path('/tmp/zfc243-calibration-plan')
SRC=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProgramRouting245.lean'
ARCH=Path('/tmp/zfc244-d91a27b462-inspection/zfc244-loop-rotation-20261018/zfc244-loop-rotation-20261018')
OLD=ARCH/'reference/baseline245/certificate/sites_logical.json'
NEW=ARCH/'machine/sites_logical.json'
PARENT=Path('/tmp/zfc-routing245-endpoint-actual/run2/verification.json')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
text=SRC.read_text()
matches=re.findall(r'^private def row(\d+) : Row := (.+)$',text,re.M)
assert len(matches)==203 and [int(i)for i,_ in matches]==list(range(203))
rows=[]
for i,body in matches:
    edges=re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?',body)
    assert len(edges)==2
    rows.append([(k,int(v)if v else None)for k,v in edges])
    assert all(k!='node' or v<int(i) for k,v in rows[-1])
# Check the actual balanced lookup syntax rather than assuming its row numbering.
raw=text.split('private def rawLookup (n : Nat) : Row :=',1)[1].split('\ndef nodes ',1)[0]
tokens=re.findall(r'if|n|<|\d+|then|else|row\d+',raw)
pos=0
def parse():
    global pos
    tok=tokens[pos];pos+=1
    if tok.startswith('row'):return ('row',int(tok[3:]))
    assert tok=='if' and tokens[pos:pos+2]==['n','<'];pos+=2
    bound=int(tokens[pos]);pos+=1
    assert tokens[pos]=='then';pos+=1
    yes=parse();assert tokens[pos]=='else';pos+=1
    no=parse();return ('if',bound,yes,no)
lookup=parse();assert pos==len(tokens)
def lookup_at(t,n):
    if t[0]=='row':return t[1]
    return lookup_at(t[2]if n<t[1]else t[3],n)
assert [lookup_at(lookup,n)for n in range(203)]==list(range(203))
assert 'if n < 203 then rawLookup n else (.halt, .halt)' in text
assert re.search(r'def program : Program where\s+nodes := nodes\s+root := 202\s+nnodes := 203',text)

modified=[list(x)for x in rows]
modified[5]=[('decnz',6),('cont',2)]
modified[6]=[('inc',0),('node',5)]
labels={'inc':'CI','decnz':'CD','brk':'CB','cont':'CC','halt':'CH'}
def unfold(table):
    leaves=[];uses={i:[]for i in range(203)};seen=set()
    def edge(e,path):
        k,v=e
        if k=='node':
            seen.add(v);uses[v].append(path)
            edge(table[v][0],path+'0');edge(table[v][1],path+'1')
        else:leaves.append([path,labels[k],v])
    edge(('node',202),'')
    return leaves,uses,seen
old,olduses,oldseen=unfold(rows);new,newuses,newseen=unfold(modified)
oldref=json.loads(OLD.read_text());newref=json.loads(NEW.read_text())
assert old==oldref and new==newref
assert len(old)==6460 and len(new)==6459 and max(len(x[0])for x in new)==51
assert olduses[6]==newuses[6]==['011']
assert newuses[4]==[] and oldseen-newseen=={4}
assert rows[4:7]==[[('inc',0),('cont',2)],[('decnz',6),('node',4)],[('node',5),('inc',0)]]
assert old[:6]==new[:6] and old[10:]==new[9:]
refs={i:[[n,side]for n,row in enumerate(rows)for side,e in enumerate(row)if e==('node',i)]for i in [4,5,6]}
assert refs=={4:[[5,1]],5:[[6,0]],6:[[7,1]]}
# Minimal height/escape certificates for the existing RMEquiv.WF checker.
def wf_tables(table):
    H=[];B=[];C=[]
    def h(e):return H[e[1]]if e[0]=='node'else 0
    def b(e):return B[e[1]]if e[0]=='node'else(1 if e[0]=='decnz'else e[1]if e[0]=='brk'else 0)
    def c(e):return C[e[1]]if e[0]=='node'else(e[1]if e[0]=='cont'else 0)
    for n,(a,z)in enumerate(table):
        H.append(1+max(h(a),h(z)));B.append(max(max(0,b(a)-1),b(z)));C.append(max(c(a),max(0,c(z)-1)))
        assert h(a)<H[n] and h(z)<H[n] and b(a)<=B[n]+1 and b(z)<=B[n] and c(a)<=C[n] and c(z)<=C[n]+1
    assert H[202]==51 and B[202]==C[202]==0
    return dict(height=H,break_escape=B,continue_escape=C)
wf=dict(original=wf_tables(rows),rotated=wf_tables(modified))
(BASE/'wf-candidate-tables.json').write_text(json.dumps(wf,indent=2)+'\n')
assert sha(PARENT)=='41ff9364f37d9eb33ff1eb2b4bbc0e5f17f0a44ac02a4a7dcdbdfa6c5b1ccf87'
parent=json.loads(PARENT.read_text());assert parent['status']=='PASS'
allpairs={q['module']:q for q in parent['reused_modules']}
needed=set()
def visit(m):
    if m in ('Init','Lean.Elab.Tactic.Omega'):return
    if m in needed:return
    q=allpairs[m];needed.add(m)
    assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['object_sha256']
    for n in re.findall(r'^import\s+(\S+)\s*$',Path(q['source']).read_text(),re.M):visit(n)
visit('BusyBeaver.ZFC.ProgramRouting245');assert len(needed)==5
provider=[allpairs[n]for n in sorted(needed)]
receipt=dict(status='STATIC_DAG_IDENTITY_AND_INTERFACE_ONLY',script=desc(__file__),inputs=[desc(p)for p in (SRC,OLD,NEW,PARENT)],program_source=desc(BASE/'ProgramRotation244.lean'),audit=desc(BASE/'Audit.lean'),proof_or_supplied_execution=False,simulation_executed=False,storage_rows=203,root=202,modified_rows=[5,6],unreachable_new_row=4,unique_changed_subtree_path='011',unfolded_leaves=dict(old=6460,new=6459),maximum_depth=51,local_old_rows=rows[4:7],local_new_rows=modified[4:7],exclusive_references=refs,unchanged_prefix_leaves=6,unchanged_suffix_leaves=6450,wf_candidate_tables=desc(BASE/'wf-candidate-tables.json'),future_first_unit_project_providers=provider,existing_provider_attestation='Selected exact current pairs from the previously actual-checked BinaryRouting245 record; this script does not claim fresh elaboration or regenerate those objects.',kernel_claims_pending=['ProgramRotation244 source and audit','old and new RMEquiv.WF certificates','rotated RMDag loop totality and contextual Run equivalence','RegisterPath halting transfer','new literal machine runtime coverage and blank startup'],findings=[])
(BASE/'static-dag-review.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(desc(BASE/'static-dag-review.json')))
