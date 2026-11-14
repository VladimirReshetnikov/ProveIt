#!/usr/bin/env python3
"""Independent PA194H6 source/table binding audit, without compiler imports."""
from pathlib import Path
import json,collections,sys,hashlib,importlib.util
ROOT=Path(sys.argv[1] if len(sys.argv)>1 else str(Path(__file__).resolve().parent.parent))
OUT=Path(sys.argv[2] if len(sys.argv)>2 else str(Path(__file__).resolve().parent/'pa194h6_structure_review.json'))
grammar=json.loads((ROOT/'construction/inputs/pa194.grammar.json').read_text())
nodes6=json.loads((ROOT/'machine/nodes.json').read_text())
nodes4=dict(nodes6);nodes4['node61']=['node60','node60']

def expand_source(nodes):
    leaves=[];named=collections.defaultdict(list)
    def walk(t,path,active):
        if isinstance(t,str):
            assert t not in active
            lo=len(leaves)
            definition=grammar['root'] if t=='x67' else grammar['rules'][t] if t in grammar['rules'] else nodes[t]
            walk(definition,path,active | {t})
            named[t].append((path,lo,len(leaves)))
        elif t[0]=='leaf':leaves.append((path,t[1],t[2] if len(t)>2 else None))
        else:
            assert len(t)==2
            walk(t[0],path+(0,),active);walk(t[1],path+(1,),active)
    walk('node172',(),frozenset())
    trie={}
    for i,(path,op,arg) in enumerate(leaves):
        at=trie
        for bit in path:at=at.setdefault(bit,{})
        assert not at;at['index']=i
    def locate(path):
        at=trie
        for j,bit in enumerate(path):
            if 'index' in at:
                assert all(b==0 for b in path[j:]);return at['index']
            at=at[bit]
        while 'index' not in at:at=at[0]
        return at['index']
    def successor(path):
        zero_positions=[i for i,b in enumerate(path) if b==0]
        assert zero_positions
        j=zero_positions[-1]
        return locate(path[:j]+(1,))
    def ancestor(path,bit,k):
        positions=[i for i,b in enumerate(path) if b==bit]
        assert k>0 and len(positions)>=k
        return path[:positions[-k]]
    resolved=[]
    for path,op,arg in leaves:
        if op=='inc':r=['inc',arg,successor(path)]
        elif op=='dec':r=['dec',arg,successor(ancestor(path,0,1)),successor(path)]
        elif op=='breakTo':r=['jump',successor(ancestor(path,0,arg))]
        elif op=='continueTo':r=['jump',locate(ancestor(path,1,arg))]
        else:assert op=='halt';r=['halt']
        resolved.append(r)
    return leaves,named,resolved

a4,m4,c4=expand_source(nodes4);a6,m6,c6=expand_source(nodes6)
assert c4==json.loads((ROOT/'construction/inputs/pa194H.instructions.json').read_text())
assert c6==json.loads((ROOT/'machine/instructions.json').read_text())
assert [[''.join(map(str,p)),op,arg]for p,op,arg in a6]==json.loads((ROOT/'machine/sites.json').read_text())
assert len(c4)==3653 and len(c6)==3775
# Multiplication is changed only inside formula Cons, never a literal tag.
assert len(m4['node61'])==len(m6['node61'])==61
for named in (m4,m6):
    cons_paths={p for p,lo,hi in named['node65']}
    assert len(cons_paths)==61
    for p,lo,hi in named['node61']:
        assert p[-4:]==(1,1,1,0) and p[:-4] in cons_paths
assert 'node61' not in json.dumps(grammar)
# Exact relocation outside the widened multiplication bodies.
sp4=sorted(m4['node61'],key=lambda v:v[1]);sp6=sorted(m6['node61'],key=lambda v:v[1])
relocate={};inside4=set();inside6=set();cursor4=cursor6=0
for (_,lo4,hi4),(_,lo6,hi6)in zip(sp4,sp6):
    assert lo4-cursor4==lo6-cursor6
    relocate.update({i:cursor6+i-cursor4 for i in range(cursor4,lo4)})
    relocate[lo4]=lo6
    assert hi4-lo4==4 and hi6-lo6==6
    for i in range(lo4,hi4):assert c4[i]==['inc',1,i+1]
    for i in range(lo6,hi6):assert c6[i]==['inc',1,i+1]
    inside4.update(range(lo4,hi4));inside6.update(range(lo6,hi6))
    cursor4,cursor6=hi4,hi6
assert len(c4)-cursor4==len(c6)-cursor6
relocate.update({i:cursor6+i-cursor4 for i in range(cursor4,len(c4))})
for i,row in enumerate(c4):
    if i in inside4:continue
    offset=2 if row[0]in ('inc','dec') else 1
    assert all(target in relocate for target in row[offset:])
    assert c6[relocate[i]]==row[:offset]+[relocate[target] for target in row[offset:]]
# Inspect literal Cons relative rows in each occurrence, covering all multiplier uses.
fixed={0:['dec',2,8,1],1:['inc',7,2],2:['dec',6,4,3],3:['jump',7],4:['dec',7,7,5],5:['inc',6,6],6:['jump',4],7:['jump',0],8:['dec',7,11,9],9:['inc',2,10],10:['jump',8],11:['dec',1,15,12],12:['inc',7,13],13:['inc',6,14],14:['jump',11],15:['dec',6,21,16],16:['inc',7,17],17:['dec',6,20,18],18:['inc',1,19],19:['jump',17],20:['jump',11],21:['dec',7,29,22],28:['jump',21]}
for offset in range(22,28):fixed[offset]=['inc',1,offset+1]
for path,lo,hi in m6['node65']:
    assert hi-lo==29
    for offset,row in fixed.items():
        split=2 if row[0]in('inc','dec')else 1
        assert c6[lo+offset]==row[:split]+[lo+t for t in row[split:]]
# Literal row edits relative to independently supplied N6.
def table(p):
    out={}
    for line in p.read_text().splitlines():
        if not line.strip()or line.startswith('#'):continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n));assert(q,b)not in out
        out[q,b]=(w,d,n)
    return out
n6=table(Path(__file__).resolve().parent/'review_inputs/pa194n6.native.tm')
h6=table(ROOT/'machine/machine.native.tm');assert set(n6)==set(h6)
expected={(38,0):((0,'R',28),(0,'R',11)),(38,1):((1,'R',20),(1,'R',122)),(214,0):((0,'R',188),(0,'R',312)),(214,1):((1,'R',312),(1,'R',20)),(312,0):((0,'R',11),(0,'R',188))}
changes={key:(n6[key],h6[key]) for key in h6 if n6[key]!=h6[key]};assert changes==expected
labels=json.loads((ROOT/'machine/labels.json').read_text());dense=table(ROOT/'machine/machine.tm')
assert len(labels)==195 and len(set(labels))==195 and labels[0]==74 and labels[-1]==254
assert len(dense)==len(h6)==388
assert {(labels[q],b):(w,d,labels[n]) for(q,b),(w,d,n)in dense.items()}==h6
# Execute the reviewed symbolic command identities without modifying the package.
spec=importlib.util.spec_from_file_location('h6commands',ROOT/'proof/check_commands.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
commands={'emitter':mod.emitter_check(),'word_checks':mod.word_check()}
result={'status':'PASS','candidate_sha256':hashlib.sha256((ROOT/'machine/machine.tm').read_bytes()).hexdigest(),'independent_tree_and_trie_resolver':True,'source4_equals_supplied_H4':True,'source4_sites':len(c4),'source6_sites':len(c6),'cons_blocks':61,'every_multiplier_is_exact_Cons_relative_1110':True,'no_direct_AX_multiplier_tag_use':True,'outside_sites_exactly_relocated':len(c4)-len(inside4),'all_61_Cons_bodies_match_generic_arithmetic_lemma':True,'literal_N6_to_H6_rows':[{ 'state':q,'read':b,'old':a,'new':v}for(q,b),(a,v)in changes.items()],'dense_native_conjugacy':True,'reviewed_original_command_checker':commands,'scope':'Independent finite source and literal table binding plus reviewed free-term word checker. Does not rerun physical symbolic contracts or export an internal PA proof object.'}
OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
