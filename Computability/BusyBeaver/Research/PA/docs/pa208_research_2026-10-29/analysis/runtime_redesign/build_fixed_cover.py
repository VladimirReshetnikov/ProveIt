"""Build fixed-role cover/gated-vacuity source variants.
No external dependencies. All source edits occur in a closed arithmetic block.
"""
from pathlib import Path
import sys, json, re, functools, hashlib, importlib.util
BASE=Path('upstream/U208_ConPA_2026-10-29/U208_ConPA_2026-10-29')
LINEAGE=Path('analysis/emitter/lineage/U214_ConPA_Reduction_2026-10-28')
OUT=Path('analysis/runtime_redesign/fixed_cover')
OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(BASE/'code'))
import source_language as s
spec=importlib.util.spec_from_file_location('role_builder',LINEAGE/'code/build_source.py')
br=importlib.util.module_from_spec(spec);spec.loader.exec_module(br)
D={}
for n,a,b in re.findall(r'\| (\d+) => \(([^,]+), ([^)]+)\)',(LINEAGE/'inputs/DagPerm.v').read_text()):D[int(n)]=(a,b)
# Existing source swaps these independent increments; no branch enters their second leaf.
D[188]=('EInc 7','EInc 6')
D[190]=('EInc 1','EInc 6')

def edge(e):
    if e.startswith('ENode '):return node(int(e[6:]))
    if e=='EHalt':return ('CH',None)
    op,n=e.split();return ({'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC'}[op],int(n))
@functools.cache
def node(n):return tuple(edge(x) for x in D[n])

def serial(parts):return parts[0] if len(parts)==1 else (parts[0],serial(parts[1:]))

def mov(src,dst):return (('CD',src),(('CI',dst),('CC',2)))
def dup(src,dst1,dst2):return (('CD',src),((('CI',dst1),('CI',dst2)),('CC',2)))
def clear(r):return (('CD',r),('CC',1))
M={f'm{n}':node(n) for n in [166,121,168,119,180,181,218,192,131,211,197,171,177,170,162,117,216]}
M['pairquad']=(M['m162'],M['m117'])
M['n18']=(('CI',7),(('CI',7),M['pairquad']))
M['rleft0']=(M['pairquad'],('CI',1))
M['rleft1']=(('CI',6),M['rleft0'])
M['qleft1']=(M['rleft1'],('CI',1))
M['qleft0']=(M['rleft0'],('CI',1))
M['rright1']=(M['n18'],('CI',1))
M['rright0']=(M['m216'],M['rleft0'])
M.update(dup_a_H_Y=dup(4,5,7),move_Y_a=mov(7,4),clear_a=clear(4),
         move_top_H=mov(1,5),dup_a_top_X=dup(4,1,6),move_X_a=mov(6,4),clear_H=clear(5),
         dup_Y_X_c=dup(7,6,3),clear_c=clear(3),dup_c_top_X=dup(3,1,6),move_X_c=mov(6,3),
         move_c_a=mov(3,4),set_c_one=('CI',3),consume_c_clear_a=(('CD',3),clear(4)))
for key,tree in M.items():assert s.boundary(tree)==(0,0,False),(key,s.boundary(tree))

V=['m166','m121','m181','m168','m166','m121','m181','m180','m119']
old_cov=json.loads((LINEAGE/'inputs/tokens.json').read_text())
old_gate=['m192','m131','m211','m197','m131']
new_gate=['m192','m131','m211','dup_a_H_Y','m131','move_Y_a']
combine=['m119','m218']
fixed_cov=[{'m168':'m177','m121':'m171'}.get(x,x) for x in old_cov]
# Independently compile the shared-expression AST into postfix load/constructor macros.
a='a';zero='zero';one='one';E='cached_E'
I=lambda x,y:('I',x,y);Q=lambda x,y:('Q',x,y);R=lambda x,y:('R',x,y);N=lambda x:('N',x)
G=Q(a,I(R(a,one),R(a,zero)))
U=Q(one,I(E,a));L=Q(one,I(a,I(G,E)));H=Q(a,I(U,N(L)))
def word(t):
    if isinstance(t,str):return [{'a':'m166','one':'m177','zero':'m171','cached_E':'m121'}[t]]
    if t[0]=='N':return word(t[1])+['m218']
    return word(t[1])+word(t[2])+[{'I':'m119','Q':'m180','R':'m181'}[t[0]]]
def direct_word(t):
    if isinstance(t,str):return word(t)
    if t[0]=='N':return direct_word(t[1])+['n18']
    if t[0] in ['Q','R'] and t[1] in ['one','zero']:
        return direct_word(t[2])+[('q' if t[0]=='Q' else 'r')+'left'+('1' if t[1]=='one' else '0')]
    if t[0]=='R' and t[2] in ['one','zero']:
        return direct_word(t[1])+['rright'+('1' if t[2]=='one' else '0')]
    return direct_word(t[1])+direct_word(t[2])+[{'I':'m119','Q':'m180','R':'m181'}[t[0]]]
shared_cov=word(H)
assert shared_cov[0]=='m166'
W={
 'fixed31':V+new_gate+fixed_cov+combine+['clear_a'],
 'cached67':V+new_gate+['m177','m166','m181','move_top_H','dup_a_top_X','move_X_a']+
             shared_cov[1:]+combine+['clear_H','clear_a']
}
c_gate=['m192','m131','dup_Y_X_c','m197','m131']
c_cov=[{'m166':'m168','m168':'m177','m121':'m171'}.get(x,x) for x in old_cov]
c_shared=[{'m166':'m168'}.get(x,x) for x in shared_cov]
W['fixed_c34']=V+c_gate+c_cov+combine+['clear_c']
W['cached_c70']=V+c_gate+['m177','m168','m181','move_top_H','dup_c_top_X','move_X_c']+c_shared[1:]+combine+['clear_H','clear_c']
W['early_literal_plus8']=V+new_gate+['set_c_one']+old_cov+combine+['consume_c_clear_a']
W['early_c_literal_plus8']=V+c_gate+['move_c_a','set_c_one']+old_cov+combine+['consume_c_clear_a']
W['fixed_after37']=V+fixed_cov+combine+old_gate
W['fixed_c_after37']=V+c_cov+combine+old_gate
W['fixed_b_after37']=V+[{'m166':'m121','m168':'m177','m121':'m171'}.get(x,x) for x in old_cov]+combine+old_gate
AFTER={key:{'matrix':matrix,'test':1,'source':0,'outer_swap':False,'lower_swap':False,'zero_guard':False}
       for key,matrix in [('fixed_after37','a'),('fixed_c_after37','c'),('fixed_b_after37','b')]}
for matrix,r in [('a',4),('b',5),('c',3)]:
    # If selector is zero, replace H by F. Otherwise leave both unchanged.
    M['false_if_zero_'+matrix]=((('CD',r),(('CI',r),('CB',1))),(clear(1),('CI',1)))
    assert s.boundary(M['false_if_zero_'+matrix])==(0,0,False)
for matrix in ['a','c','b']:
    for outer_swap,lower_swap in [(False,True),(True,False),(True,True)]:
        key=f'fixed_{matrix}_o{int(outer_swap)}l{int(lower_swap)}_37'
        AFTER[key]={'matrix':matrix,'test':1,'source':0,'outer_swap':outer_swap,'lower_swap':lower_swap,'zero_guard':False}
    key=f'fixed_{matrix}_swap35'
    AFTER[key]={'matrix':matrix,'test':0,'source':1,'outer_swap':False,'lower_swap':False,'zero_guard':True}
for outer_swap,lower_swap in [(False,False),(False,True),(True,False),(True,True)]:
    key=f'direct_a_o{int(outer_swap)}l{int(lower_swap)}'
    AFTER[key]={'matrix':'a','test':1,'source':0,'outer_swap':outer_swap,'lower_swap':lower_swap,'zero_guard':False,'direct':True}
AFTER['direct_a_swap']={'matrix':'a','test':0,'source':1,'outer_swap':False,'lower_swap':False,'zero_guard':True,'direct':True}
for key,config in AFTER.items():
    matrix=config['matrix'];test='one' if config['test']==1 else 'zero';src='one' if config['source']==1 else 'zero'
    e=R(test,a);g=Q(a,I(R(a,test),R(a,src)))
    u=Q(test,I(e,a))
    l=Q(test,I(g,I(a,e))) if config['lower_swap'] else Q(test,I(a,I(g,e)))
    h=Q(a,I(l,N(u))) if config['outer_swap'] else Q(a,I(u,N(l)))
    cov=[{'m166':{'a':'m166','b':'m121','c':'m168'}[matrix]}.get(x,x) for x in (direct_word(h) if config.get('direct') else word(h))]
    W[key]=V+cov+(['false_if_zero_'+matrix] if config['zero_guard'] else [])+(['m119','n18'] if config.get('direct') else combine)+old_gate
old_word=V+old_cov+combine+old_gate
old_sites=json.loads((BASE/'machine/sites.json').read_text());old_tree=s.tree(old_sites)
old_graph=s.graph_intervals(old_sites)
# Reuse the exact existing subtree for every CFG-equivalent macro.
old_nodes=set()
def visit_old(t):
    if t in old_nodes:return
    old_nodes.add(t)
    if not s.leaf(t):visit_old(t[0]);visit_old(t[1])
visit_old(old_tree)
macro_reassociations={}
old_reassociations={}
for name,t in list(M.items()):
    matches=[u for u in old_nodes if br.size(u)==br.size(t) and s.boundary(u)==s.boundary(t)
             and s.graph_intervals(s.sites(u))==s.graph_intervals(s.sites(t))]
    if matches:
        assert len(matches)==1,(name,len(matches))
        macro_reassociations[name]=t!=matches[0]
        M[name]=matches[0]
        old_reassociations[t]=matches[0]
def reuse_components(t):
    if t in old_reassociations:return old_reassociations[t]
    if s.leaf(t):return t
    return (reuse_components(t[0]),reuse_components(t[1]))
for name,t in list(M.items()):M[name]=reuse_components(t)
LO,HI=2642,3766
assert sum(br.size(M[x]) for x in old_word)==HI-LO
# Match all old primitive effects and control edges against this macro inventory.
expected=[];at=LO
for name in old_word:
    t=M[name];rows=s.sites(t);g=s.graph_intervals(rows)
    n=len(rows)
    # Standalone resolver wraps normal exits to zero. Reconstruct boundaries directly.
    bounds={}
    for i,(p,op,arg) in enumerate(rows):
        for j in range(len(p)+1):
            v=p[:j]
            if v not in bounds:bounds[v]=[i,i+1]
            else:bounds[v][1]=i+1
    for i,(p,op,arg) in enumerate(rows):
        if op=='CI':ds=[i+1];effect=['increment',arg]
        elif op=='CH':ds=[];effect=['halt']
        else:
            which='1' if op=='CC' else '0';cnt=arg if op!='CD' else 1
            ix=[j for j,c in enumerate(p) if c==which]
            assert len(ix)>=cnt,(name,p,op,arg)
            anc=p[:ix[-cnt]];target=bounds[anc][0 if op=='CC' else 1]
            ds=[target,i+1] if op=='CD' else [target]
            effect=['decrement',arg] if op=='CD' else ['identity']
        expected.append([effect,[at+d for d in ds]])
    at+=n

if old_graph[LO:HI]!=expected:
    for i,(x,y) in enumerate(zip(old_graph[LO:HI],expected)):
        if x!=y:print('DIFF',LO+i,x,y)
    raise AssertionError('Original interval does not match macro inventory')

# Exact independent symbolic arithmetic interface for the new macro words.
def symbolic(names,variant):
    # Registers0,8 are opaque and unchanged. Stack is explicitly represented above J.
    reg={1:'old_top',3:'c',4:'a',5:'b',6:0,7:0};stack=[];gate=[]
    for name in names:
        if name in ['m166','m121','m168','m177','m171']:
            assert reg[6]==reg[7]==0
            stack.append(reg[1]);reg[1]=reg[{ 'm166':4,'m121':5,'m168':3}[name]] if name in ['m166','m121','m168'] else (1 if name=='m177' else 0)
        elif name in ['m119','m180','m181']:
            assert reg[6]==reg[7]==0 and stack
            reg[1]=({'m119':'I','m180':'Q','m181':'R'}[name],stack.pop(),reg[1])
        elif name=='m218':
            assert reg[6]==reg[7]==0;reg[1]=('I',reg[1],1)
        elif name=='n18':
            assert reg[6]==reg[7]==0;reg[1]=('I',reg[1],1)
        elif name in ['qleft0','qleft1','rleft0','rleft1','rright0','rright1']:
            assert reg[6]==reg[7]==0
            k=int(name[-1]);op='Q' if name[0]=='q' else 'R'
            reg[1]=(op,reg[1],k) if 'right' in name else (op,k,reg[1])
        elif name=='m192':
            assert reg[6]==reg[7]==0;reg[6]=reg[7]=reg[3];reg[3]=0
        elif name=='m131':
            gate.append([reg[6],reg[5]])
            reg[1]=('if_eq',reg[6],reg[5],0,reg[1]);reg[6]=reg[5]=0
        elif name=='m211':assert reg[6]==0;reg[6]=reg[7];reg[7]=0
        elif name=='m197':assert reg[5]==0;reg[5]=reg[4];reg[4]=0
        elif name=='dup_Y_X_c':assert reg[6]==reg[3]==0;reg[6]=reg[3]=reg[7];reg[7]=0
        elif name=='dup_a_H_Y':assert reg[5]==reg[7]==0;reg[5]=reg[7]=reg[4];reg[4]=0
        elif name=='move_Y_a':assert reg[4]==0;reg[4]=reg[7];reg[7]=0
        elif name=='move_top_H':assert reg[5]==0;reg[5]=reg[1];reg[1]=0
        elif name=='dup_a_top_X':assert reg[1]==reg[6]==0;reg[1]=reg[6]=reg[4];reg[4]=0
        elif name=='move_X_a':assert reg[4]==0;reg[4]=reg[6];reg[6]=0
        elif name=='dup_c_top_X':assert reg[1]==reg[6]==0;reg[1]=reg[6]=reg[3];reg[3]=0
        elif name=='move_X_c':assert reg[3]==0;reg[3]=reg[6];reg[6]=0
        elif name=='move_c_a':assert reg[4]==0;reg[4]=reg[3];reg[3]=0
        elif name=='set_c_one':assert reg[3]==0;reg[3]=1
        elif name=='consume_c_clear_a':assert reg[3]==1;reg[3]=reg[4]=0
        elif name=='clear_c':reg[3]=0
        elif name=='clear_a':reg[4]=0
        elif name=='clear_H':reg[5]=0
        elif name.startswith('false_if_zero_'):
            matrix=name[-1];reg[1]=('if_eq',reg[{'a':4,'b':5,'c':3}[matrix]],0,1,reg[1])
        else:raise ValueError(name)
    exactV=I(R('a','b'),Q('c',R('a','b')))
    gated=('if_eq','c','a',0,('if_eq','c','b',0,exactV))
    config=AFTER.get(variant,{})
    matrix=config.get('matrix','c' if 'dup_Y_X_c' in names else 'a')
    test=config.get('test',1);src=config.get('source',0)
    exactE=R(test,matrix);exactG=Q(matrix,I(R(matrix,test),R(matrix,src)))
    exactU=Q(test,I(exactE,matrix))
    exactL=Q(test,I(exactG,I(matrix,exactE))) if config.get('lower_swap') else Q(test,I(matrix,I(exactG,exactE)))
    exactH=Q(matrix,I(exactL,I(exactU,1))) if config.get('outer_swap') else Q(matrix,I(exactU,I(exactL,1)))
    if config.get('zero_guard'):exactH=('if_eq',matrix,0,1,exactH)
    if variant in AFTER:
        target=('if_eq','c','a',0,('if_eq','c','b',0,I(I(exactV,exactH),1)))
    else:target=I(I(gated,exactH),1)
    assert reg[1]==target,(reg[1],target)
    assert all(reg[k]==0 for k in [3,4,5,6,7]),reg
    assert stack==['old_top'],stack
    return {'final_top':target,'stack':'[old_top; original_stack]','zeroed_registers':[3,4,5,6,7],
            'unchanged_registers':[0,8],'gate_comparisons':gate,'clean_scratch_each_constructor':True}

reports={}
for key,names in W.items():
    t=serial([M[name] for name in names]);assert s.boundary(t)==(0,0,False)
    prefix=br.closed_forest(old_tree,158,LO)
    repl=serial(prefix+[t,('CB',1)])
    assert s.boundary(repl)==s.boundary(s.subtree(old_tree,'001100111'))
    tree=s.replace(old_tree,'001100111',repl);rows=s.sites(tree)
    g,checks=s.graph_arithmetic(rows);assert g==s.graph_intervals(rows)
    delta=len(rows)-len(old_sites)
    shift=lambda i:i if i<HI else i+delta
    for i in list(range(LO))+list(range(HI,len(old_sites))):
        eff,targets=old_graph[i]
        assert all(not LO<j<HI for j in targets),('external incoming edge',i,targets)
        assert g[shift(i)]==[eff,[shift(j) for j in targets]],('external mismatch',i)
    raw=s.compact(rows);(OUT/(key+'.sites.json')).write_bytes(raw)
    (OUT/(key+'.macros.json')).write_text(json.dumps(names,indent=2)+'\n')
    (OUT/(key+'.tree.json')).write_text(json.dumps(tree,separators=(',',':'))+'\n')
    reports[key]={'metrics':s.metrics(tree),'replacement_primitives':br.size(t),'old_interval':[LO,HI],
                  'new_interval':[LO,HI+delta],'primitive_saving':-delta,
                  'source_sha256':hashlib.sha256(raw).hexdigest(),
                  'initial_136_sites_equal':rows[:136]==old_sites[:136],
                  'startup_site_136_equal':rows[136]==old_sites[136],
                  'exterior_cfg_identity':True,'independent_cfg_resolvers_agree':True,
                  'arithmetic_successor_checks':checks,'symbolic_interface':symbolic(names,key)}
(OUT/'build_receipt.json').write_text(json.dumps(reports,indent=2)+'\n')
(OUT/'macro_trees.json').write_text(json.dumps(M,separators=(',',':'))+'\n')
if __name__=='__main__':
    for k,v in reports.items():print(k,json.dumps({a:b for a,b in v.items() if a!='symbolic_interface'},indent=2))
