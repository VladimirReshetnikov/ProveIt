#!/usr/bin/env python3
"""Reproduce the package's exact positive results and one rejected195 witness.

Python3.10+; standard library only. All release checks use explicit exceptions
and remain enabled with python -O. No bounded register sampling substitutes
for the symbolic source contracts.
"""
from pathlib import Path
import sys,json,hashlib,time,subprocess
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'verification'))
sys.path.insert(0,str(ROOT/'math_reduction/folding'))
sys.path.insert(0,str(ROOT/'comparison/audit'))
import symbolic as S
import compile_grammar as C
import compatible_folds as F
import check_raw_startup as B
import verify_renaming as R

def require(ok,msg):
    if not ok:raise ValueError(msg)
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def sites_from(path):return freeze(json.loads(Path(path).read_text()))
def check_source(table,sites,expected_states=196):
    m=B.load(table);states={q for q,b in m};targets={z for w,d,z in m.values()}
    require(states==set(range(expected_states)),'incorrect working-state domain')
    require(targets-states=={expected_states},'incorrect halt label')
    require(len(m)==2*expected_states,'incorrect transition-row count')
    require(set(m)=={(q,b)for q in states for b in (0,1)},'incomplete binary table')
    require(all(w in (0,1)and d in(-1,1)for w,d,z in m.values()),'invalid binary action')
    require(S.check_engine(m),'an unbounded-engine obligation changed')
    require(max(len(p)for p,op in sites)<=48,'frame gap would be too short')
    old=S.all_sites;old_halt=S.HALT;S.all_sites=lambda:sites;S.HALT=expected_states
    lengths=[]
    try:
        for i,branch,br,start,target in S.contracts():
            result=S.execute(m,br,start,target)
            require(result is not None,('source contract failed',table.name,i,branch))
            lengths.append(result[0])
    finally:S.all_sites=old;S.HALT=old_halt
    return {'states':expected_states,'rows':2*expected_states,'sites':len(sites),'contracts':len(lengths),
        'max_path':max(len(p)for p,op in sites),'max_symbolic_steps':max(lengths),
        'sum_symbolic_steps':sum(lengths),'all_contracts_pass':True,'sha256':sha(table)}

def rejected_witness():
    candidate=ROOT/'verification/candidates/warm_physical_61_8047.tm'
    data=json.loads((ROOT/'verification/candidates/warm_physical_61_8047.json').read_text())
    sites=S.flatten(freeze(data['tree']));path=sites[1111][0]
    m=B.load(candidate);ones=B.frame_ones(path,vs=[0]*9+[1]*26);state=75;head=0
    seen={};states=[]
    for step in range(3000):
        key=(state,head,frozenset(ones))
        if key in seen:
            begin=seen[key]
            require(step>begin,'empty cycle')
            return {'states':len(m)//2,'source_site':1111,'path':path,
                'initial_frame_valid':True,'first_cycle_step':begin,
                'repeat_step':step,'literal_period':step-begin,
                'cycle_states':states[begin:],'outcome':'exact finite-tape cycle',
                'scope':'refutes the proposed source-simulation contract'}
        seen[key]=step;states.append(state)
        row=m.get((state,int(head in ones)))
        require(row is not None,'rejected-candidate diagnostic unexpectedly halted')
        w,d,state=row
        if w:ones.add(head)
        else:ones.discard(head)
        head+=d
    raise ValueError('rejected-candidate cycle was not reproduced')

def append_zero_witness():
    m=S.load_machine();require(m[125,0]==(1,-1,39),'append-one row changed')
    m[125,0]=(0,-1,39)
    ones=set();q=0;head=0
    for step in range(76):
        w,d,q=m[q,int(head in ones)]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=d
    require((q,head,ones)==(35,4,{-3,1}),'append-zero failure was not reproduced')
    require(m[35,0]==(1,1,35),'rightward blank-scan row changed')
    return {'step':76,'state':q,'head':head,'ones':sorted(ones),
        'loop_row':[1,'R',35],
        'reason':'Every cell at or right of the head is zero; each step writes behind the new head and moves right in the same state.',
        'scope':'rejects this initialization for the proposed source simulation'}

def integrated_source():
    import integrated_flexible as IF
    G=IF.G;O=IF.O
    require(len(G.ORIG)==201 and len(G.WORD)==196,'macro-word counts changed')
    require(G.WORD==G.ORIG[:86]+G.ORIG[102:185]+G.HEADS[4][:-3]+G.ORIG[187:],
        'integrated witness word differs from the stated edit')
    def unneg(t):
        require(isinstance(t,tuple)and len(t)==3 and t[0]==0 and t[2]==1,'negation expected')
        return t[1]
    x=unneg(G.expression(G.HEADS[4]))
    old_chain=unneg(G.expression(G.SUFFIX[:-3]));_,eq,rest=old_chain;_,mem,q=rest
    qtag,inner,c=q;itag,sep,np=inner;nptag,point,one=np
    require((qtag,itag,nptag,one)==(2,0,0,1),'old gate expression changed')
    expected=(0,(0,eq,(0,mem,(2,(0,sep,(0,point,x)),c))),1)
    require(G.expression(G.GATE_WORD)==expected,'new word does not construct the specified gate')
    grammar=json.loads((ROOT/'math_reduction/folding/integrated_start.json').read_text())
    t=G.decode(grammar['rules'],grammar['root'])
    require(t==G.START,'integrated grammar differs from the exact source edit')
    tree=O.C.replace(O.ROOT,O.RAW['x67'],O.raw(t));sites=tuple(O.S.flatten(tree))
    require(len(sites)==3745,'integrated source-site count changed')
    require(sum(op[0]=='dec'for p,op in sites)==1127,'integrated decrement count changed')
    require(sites==sites_from(ROOT/'comparison/audit/integrated_gate206_sites.json'),
        'integrated source reconstruction disagrees with supplied sites')
    better=json.loads((ROOT/'math_reduction/folding/integrated_best_815732.json').read_text())
    t2=G.decode(better['rules'],better['root'])
    tree2=O.C.replace(O.ROOT,O.RAW['x67'],O.raw(t2));sites2=tuple(O.S.flatten(tree2))
    require(S.instructions(sites2)==S.instructions(sites),
        '203-state grammar changes the integrated instruction graph')
    require(sites2==sites_from(ROOT/'comparison/audit/integrated_gate203_sites.json'),
        '203-state source reconstruction disagrees with supplied sites')
    return sites,sites2,{'old_macro_tokens':201,'new_macro_tokens':196,'source_sites_removed':67,
        'decrement_sites_removed':20,'exact_word_edit':True,'symbolic_gate_expression':True}

def main():
    start=time.time();receipts=ROOT/'receipts';receipts.mkdir(exist_ok=True)
    hashes=json.loads((ROOT/'input_hashes.json').read_text())
    for name,expected_hash in hashes.items():
        require(sha(ROOT/name)==expected_hash,('pinned input hash changed',name))
    reference=ROOT/'sources/BusyBeaver/data/pa196.tm'
    require(sha(reference)=='e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8','reference table hash changed')
    tree,defs=S.source_tree();baseline=S.flatten(tree);baseline_codes=S.instructions(baseline)
    audit=ROOT/'comparison/audit'
    cases=[('published196',reference,baseline,58154,196)]
    rebracket=sites_from(audit/'rebracketed196_sites.json')
    require(S.instructions(rebracket)==baseline_codes,'rebracketing changed the instruction graph')
    cases.append(('rebracketed196',audit/'rebracketed196_dense.tm',rebracket,58154,196))
    htree=C.replace(tree,defs['node170'],((defs['node36'],(defs['node167'],defs['node145'])),defs['node57']))
    hsites=S.flatten(htree)
    require(tuple(hsites)==sites_from(audit/'h_catalan_node170_3_133_37_sites.json'),'h-only tree differs from the documented change')
    cases.append(('h_only196',audit/'h_catalan_node170_3_133_37.tm',hsites,57922,196))
    isites,isites2,ireceipt=integrated_source()
    cases.append(('integrated_gate206',audit/'integrated_gate206_dense.tm',isites,59164,206))
    cases.append(('integrated_gate203',audit/'integrated_gate203_dense.tm',isites2,58154,203))
    results={'integrated_source':ireceipt}
    for name,path,sites,expected,nstates in cases:
        result=check_source(path,sites,nstates)
        sites_file=receipts/(name+'_sites.json');sites_file.write_text(json.dumps(sites))
        result['startup']=B.check(path,sites_file,expected_step=expected)
        results[name]=result
        print(name,json.dumps({k:v for k,v in result.items()if k!='startup'}),flush=True)
    naming=json.loads((audit/'rebracketed196_receipt.json').read_text())
    results['relabeling']=R.verify(ROOT/'verification/candidates/open_physical_61_201240_safe.tm',audit/'rebracketed196_dense.tm',naming['mapping'])
    inaming=json.loads((audit/'integrated_gate206_receipt.json').read_text())
    results['integrated_relabeling']=R.verify(ROOT/'math_reduction/folding/integrated_start.tm',audit/'integrated_gate206_dense.tm',inaming['mapping'])
    inaming2=json.loads((audit/'integrated_gate203_receipt.json').read_text())
    results['integrated203_relabeling']=R.verify(ROOT/'math_reduction/folding/integrated_best_815732.tm',audit/'integrated_gate203_dense.tm',inaming2['mapping'])
    data=json.loads((ROOT/'verification/open_physical_61_201240.json').read_text());C.TOKENS=data['tokens']
    pure,newtree,allocated,entry=C.compile_grammar(data)
    cert=json.loads((ROOT/'verification/candidates/open_physical_61_201240_safe.json').read_text())['certificate']
    folds=[(q,r,tuple(ds))for q,r,ds in cert['folds']]
    opts=F.candidates(pure,allocated.values())
    require(all(x in opts for x in folds),'fold predecessor/helper premises failed')
    valid,blocks=F.check_local(pure,folds,record=True);require(valid,'simultaneous local fold proof failed')
    folded,mapping=F.fold(pure,folds)
    require(folded==S.load_machine(ROOT/'verification/candidates/open_physical_61_201240_safe.tm'),'folded rows differ from supplied raw table')
    require(tuple(S.flatten(newtree))==rebracket,'generated source differs from supplied sites')
    results['folds']={'pure_states':len(pure)//2,'folded_states':len(folded)//2,'pairs':folds,
        'local_blocks':[{'original':q,'predecessor':p,'read':b,'steps':len(trace)}for q,p,b,trace in blocks]}
    results['rejected195']=rejected_witness();print('rejected195',json.dumps(results['rejected195']),flush=True)
    results['append_zero_rejected']=append_zero_witness()
    subprocess.run([sys.executable,str(audit/'compare_designs.py'),'--output',str(receipts/'comparison_reproduced.json')],check=True)
    census=json.loads((receipts/'comparison_reproduced.json').read_text())
    results['comparison']={k:v for k,v in census.items()if k!='machines'}
    results['sub196_constructed']=False
    results['formal_status']='Symbolic certificate replay plus mathematical arguments; no new Lean build was performed.'
    results['seconds']=time.time()-start
    (receipts/'verification.json').write_text(json.dumps(results,indent=2)+'\n')
    print('ALL RELEASE CHECKS PASS; no verified sub196 construction is claimed.',flush=True)
if __name__=='__main__':main()
