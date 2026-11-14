#!/usr/bin/env python3
"""Portable finite replay.  This is NOT a Lean build or a PA proof checker.

All assertions use require(), so python -O does not disable this wrapper's
checks.  See report.pdf for the different mathematical scopes of the checks.
"""
from pathlib import Path
from collections import deque
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess
import sys, tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True

def require(p, message):
    if not p:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q,b,w,d,t = line.split()
        q,b,w,t = map(int,(q,b,w,t))
        require(q >= 0 and b in (0,1) and w in (0,1) and d in ('L','R'), 'bad row')
        require((q,b) not in rows, 'duplicate row')
        rows[q,b] = w,d,t
    states = {q for q,b in rows}
    require(len(rows) == 2*len(states), 'incomplete table')
    halts = {t for w,d,t in rows.values()} - states
    require(len(halts) == 1, 'not exactly one terminal label')
    require(0 in states, 'missing initial state 0')
    return rows,states,next(iter(halts))

def canonical(rows, start=0):
    """Same explicitly documented serialization as the main input census."""
    states = {q for q,b in rows}
    halts = {t for w,d,t in rows.values()} - states
    names = {start:0}; todo = deque([start]); out = []
    while todo:
        q = todo.popleft()
        if q in halts:
            continue
        for b in (0,1):
            w,d,t = rows[q,b]
            if t not in names:
                names[t] = len(names); todo.append(t)
            out.append([names[q],b,w,d,names[t]])
    require(set(names) == states|halts, 'graph-unreachable label')
    return hashlib.sha256(json.dumps(out,separators=(',',':')).encode()).hexdigest()

def blank_run(rows, steps):
    tape=set();q=0;h=0;visits=0
    for i in range(steps):
        b=int(h in tape)
        if (q,b) not in rows:
            return q,h,tape,i,visits
        visits += (q,b)==(115,1)
        w,d,q=rows[q,b]
        if w:tape.add(h)
        else:tape.discard(h)
        h += 1 if d=='R' else -1
    return q,h,tape,steps,visits

def tuple_tree(t):
    return tuple(map(tuple_tree,t)) if isinstance(t,list) else t

def source_nodes(t):
    if isinstance(t[0],str):return set()
    return {t}|source_nodes(t[0])|source_nodes(t[1])

def invoke(args, cwd=ROOT):
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
    p=subprocess.run(args,cwd=cwd,env=env,text=True,capture_output=True)
    require(p.returncode==0, f'command failed: {args}\n{p.stdout}\n{p.stderr}')
    return p.stdout.strip()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=ROOT/'verification_receipt.generated.json')
    ap.add_argument('--check-manifest',action='store_true',help='also check delivered SHA256SUMS before replay')
    args=ap.parse_args()
    record={'status':'PASS', 'scope':'finite replay; no Lean build; no new PA biconditional',
            'sub196_machine_established':False}
    if args.check_manifest:
        checked=0
        for line in (ROOT/'SHA256SUMS').read_text().splitlines():
            expected,name=line.split('  ',1)
            require(digest(ROOT/name)==expected,'checksum mismatch: '+name);checked+=1
        record['manifest_files_checked']=checked

    files={
        'published_pa196.tm':(196,'e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'),
        'published_pa209.tm':(209,'0610d978675320f0b4b1ef34619dcd3daa5912632d7037e200dfcc70954fea51'),
        'experimental_mp_without_zero_push_196.tm':(196,'3d7f91e548f8a21ed4d6eecdc1f1299d960b612912bf9a6bf7b74870c5c9f11a'),
        'experimental_mp_result_in_h_196.tm':(196,'893f08672746ea1c281fda7de4ecc7c8a75fa1f896f2255c9c00e345c37aaaca'),
    }
    tables={};table_info={}
    for name,(n,sha) in files.items():
        p=ROOT/'machines'/name;rows,states,halt=read_table(p)
        require(len(states)==n and digest(p)==sha,'table count/hash '+name)
        canonical(rows)
        tables[name]=rows
        table_info[name]={'working_states':n,'rows':len(rows),'halt':halt,'sha256':sha}
    record['tables']=table_info
    original=tables['published_pa196.tm']
    for name,target in [('experimental_mp_without_zero_push_196.tm',100),
                        ('experimental_mp_result_in_h_196.tm',108)]:
        require({k for k in original if original[k]!=tables[name][k]}=={(115,1)},'not a one-row patch')
        require(tables[name][115,1]==(1,'R',target),'incorrect MP patch')
    record['one_row_patches_checked']=2

    # Bind the finite startup to the complete published unary frame, not just
    # a sampled prefix or a register counter value.
    def startup_frame(q):
        h=-2;ones={-3,-2,46};pos=47
        for v in [0,0,0,0,0,0,2,0,0]+[1]*26:
            pos+=1;ones.update(range(pos,pos+v+1));pos+=v+1
        return q,h,ones
    startups={}
    for name,rows in tables.items():
        n=58210 if name=='published_pa209.tm' else 58154
        q=81 if name=='published_pa209.tm' else 75
        got=blank_run(rows,n)
        require(got[:3]==startup_frame(q) and got[3]==n,'full startup mismatch '+name)
        if q==75:require(got[4]==0,'modified row used during startup')
        startups[name]={'steps':n,'control':q,'head':-2,'one_cells':len(got[2]),
                        'full_frame_equality':True}
    record['startup']=startups

    manifest=json.loads((ROOT/'sources/incoming208/incoming_comparison_manifest.json').read_text())
    graph_classes={};main_count=0
    for archive in manifest['archives']:
        for item in archive['designated_main_tables']:
            p=ROOT/'sources/incoming208/extracted'/item['path']
            rows,states,halt=read_table(p);key=canonical(rows)
            require(len(states)==208,'wrong incoming state count')
            require(digest(p)==item['raw_sha256'] and key==item['canonical_sha256'],'incoming identity')
            graph_classes.setdefault(key,[]).append(item['designation']);main_count+=1
    require(main_count==9 and len(graph_classes)==2,'main census changed')
    record['incoming_main_graph_classes']=graph_classes

    for d in ('history209','incoming208','theory_audit'):
        sys.path.insert(0,str(ROOT/'sources'/d))
    sys.path.insert(0,str(ROOT/'research'))
    import grammar_search as g
    import compile_ax as ca
    from scan_threshold import frame,run
    from source_invariants import cfg,closure

    old_tree=g.parse_program(ROOT/'sources/history209/M6/Program.lean')['trie']
    new_tree=g.parse_program()['trie']
    metrics={}
    for name,tree,sites,nodes,depth in [('pa209',old_tree,3948,173,33),('pa196',new_tree,3812,159,38)]:
        flat=g.flatten(tree);actual=(len(flat),len(source_nodes(tree)),max(len(p) for p,op in flat))
        require(actual==(sites,nodes,depth),'source metrics '+name)
        metrics[name]={'sites':sites,'distinct_internal_nodes':nodes,'actual_maximum_path_bits':depth}
    record['source_metrics']=metrics

    # Reconstruct and locally certify the six published AX folds.
    ns,mac,body=ca.macro_info();unfolded,internal,root=ca.compile_tree(body,True)
    native=ca.native();tags=ca.tag_states(unfolded)[0];selection=[]
    for dropped,kept in {1304:1307,1311:1331,1315:1305,1323:1355,1325:1345,1351:1350}.items():
        hs=tuple(native[kept,b][2] if native[kept,b][1]=='L' else None for b in (0,1))
        selection.append({'s':kept,'t':dropped,'helpers':hs,'tags':(tags[kept],tags[dropped])})
    require(len(ca.states(unfolded))==202 and len(internal)==68,'unfolded count')
    require(ca.valid_selection(unfolded,selection),'local fold certificate')
    require(ca.make_fold(unfolded,selection)[0]==native,'literal decoder reconstruction')
    record['decoder_reconstruction']={'unfolded_states':202,'folds':6,'exact_196_rows':True,'AX_tokens':len(g.word(body))}

    leaves,G=cfg(new_tree)
    require(closure(G,6)[7]=={0} and closure(G,1)[3773]=={0},'forced zero guard')
    record['source_inductive_zero_guards']=[{'site':7,'register':6},{'site':3773,'register':1}]

    # Deliberately bounded primitive checks.  No universal quantifier is
    # inferred from these particular clean frames.
    labels=json.loads(re.search(r'def labels : List Nat := (\[.*\])',
        (ROOT/'sources/bb196/PA196/Conjugacy.lean').read_text()).group(1))
    inv={v:i for i,v in enumerate(labels)}
    physical=[6,2,0,4,3,7,8,5,1]
    cases={}
    for stem,table_name,expected_sites,expected_cases in [
        ('mp_no_zero_candidate','experimental_mp_without_zero_push_196.tm',3793,4933),
        ('mp_move_h_candidate','experimental_mp_result_in_h_196.tm',3789,4928)]:
        data=json.loads((ROOT/'sources/history209'/(stem+'.json')).read_text())
        tree=tuple_tree(data['tree']);flat=g.flatten(tree);instructions=g.resolve(tree)
        rows={(inv[q],b):(w,d,inv[t]) for q,b,w,d,t in data['table']}
        require(rows==tables[table_name],'native/dense binding '+stem)
        numeric={k:(w,1 if d=='R' else -1,t) for k,(w,d,t) in rows.items()}
        count=0;maxsteps=0
        for i,((path,op),inst) in enumerate(zip(flat,instructions)):
            if inst[0]=='halt':continue
            for positive in (False,True) if inst[0]=='dec' else (False,):
                values=[0]*10+[1]*25
                if inst[0]=='dec' and positive:values[physical[inst[1]]]=1
                final=values.copy();gap=0
                if inst[0]=='inc':final[physical[inst[1]]]+=1;final.append(1);j=inst[2]
                elif inst[0]=='dec':
                    if positive:final[physical[inst[1]]]-=1;gap=1;j=inst[3]
                    else:j=inst[2]
                else:j=inst[1]
                if j is None:j=0
                target=frame(flat[j][0],final,gap)
                steps,result,seen=run(numeric,frame(path,values),target)
                require(steps is not None and result==target,f'frame failure {stem} site{i} positive{positive}')
                count+=1;maxsteps=max(maxsteps,steps)
        require(len(flat)==expected_sites and count==expected_cases,'case/site count '+stem)
        cases[stem]={'sites':len(flat),'cases':count,'maximum_steps_in_test':maxsteps,
                     'scope':'one concrete clean register profile; zero and one decrement inputs'}
    record['bounded_primitive_frames']=cases

    rejected={}
    for name in ('REJECTED_shift_layout.tm','REJECTED_combined_layout.tm'):
        rows,states,halt=read_table(ROOT/'rejected'/name)
        q,h,tape,n,v=blank_run(rows,50000)
        require(q==halt and n==43563,'expected rejected first halt')
        rejected[name]={'first_halt_steps':n,'halt':q,'head':h,'one_cells':len(tape),'sha256':digest(ROOT/'rejected'/name)}
    record['rejected_blank_counterexamples']=rejected

    with tempfile.TemporaryDirectory(prefix='conpa_replay_') as directory:
        temporary=Path(directory)
        helper_output=temporary/'helpers.json'
        helper=ROOT/'sources/incoming208/helper18'
        invoke([sys.executable,str(helper/'code/verify_helper_machines.py'),'--root',str(helper),'--output',str(helper_output)])
        data=json.loads(helper_output.read_text())
        require(data['status']=='PASS' and data['machines']==18 and data['all_initial_tapes'],'helper proof replay')
        record['helper18']={k:v for k,v in data.items() if k!='results'}
        shutil.copy2(ROOT/'sources/theory_audit/command_model_checks.py',temporary/'command_model_checks.py')
        record['command_regression_stdout']=invoke([sys.executable,str(temporary/'command_model_checks.py')])
        record['bounded_command_checks']=json.loads((temporary/'command_model_checks.json').read_text())
    upstream=ROOT/'sources/bb196'
    record['upstream_publication_checks']='\n'.join(x for x in (
        invoke([sys.executable,'scripts/check_publication.py'],upstream),
        invoke([sys.executable,'scripts/pa196/generate_machine.py','--check'],upstream),
        invoke([sys.executable,'scripts/pa196/generate_challenge.py','--check'],upstream)) if x)

    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(record,indent=2)+'\n')
    print('PASS: input identities, graph comparison, 18 local helper equivalences, exact startups,')
    print('      decoder reconstruction, bounded command/frame checks, and rejected first halts.')
    print('SCOPE: no Lean build; no newly formalized PA biconditional; no sub-196 result.')
    print('Receipt:',args.output)

if __name__=='__main__':
    main()
