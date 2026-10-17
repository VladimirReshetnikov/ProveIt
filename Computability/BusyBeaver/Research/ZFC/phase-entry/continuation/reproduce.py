#!/usr/bin/env python3
"""Reconstruct and replay two fixed251-state continuation experiments.

Literal rows only: no instruction-box summaries, candidate census or Lean.
--quick uses100k moves; default uses100M moves for each saved blank control.
"""
import argparse,hashlib,importlib.util,json,subprocess,sys
from pathlib import Path

BASELINE='Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm'
SHA='939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
PROGRAM='lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
PROGRAM_SHA='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
def digest(data):return hashlib.sha256(data).hexdigest()
def write(path,data):path.write_text(json.dumps(data,indent=2)+'\n')
def tape_hash(ones):return digest(json.dumps(ones,separators=(',',':')).encode())
def frame_summary(f):
    out={k:v for k,v in f.items() if k not in ('whole_ones','final_whole_ones')}
    if 'whole_ones'in f:out['whole_tape_ones_sha256']=tape_hash(f['whole_ones'])
    return out
def summarize(work,files,origin):
    prepared=[]
    for fn in ('prepared-controls.json','source-invariant-controls.json'):
        data=json.loads((work/fn).read_text())
        for c in data['cases']:
            f=c['clean_frames'][-1]
            prepared.append({'input':c['input'],'outcome':c['outcome'],'steps':c['steps'],
              'changed_row_hits':len(c['changed_row_hits']),'final_frame':frame_summary(f),
              'whole_tape_ones_sha256':tape_hash(c['final_whole_ones']),
              'source_relation_t_eq_n_plus_k':c['input']['t']==c['input']['n']+c['input']['k']})
    blank=[]
    for name in ('R252','L229'):
        d=json.loads((work/(name+'-100m.json')).read_text())
        r=json.loads((work/(name+'-after-two-roots.json')).read_text())
        assert (r['steps'],r['state'],r['head'],r['one_count'])==(d['final']['step'],d['final']['state'],d['final']['head'],d['final']['one_count'])
        blank.append({'name':name,'status':d['status'],'final':frame_summary(d['final']),
          'first_changed_row_step':d['first_changed_row_step'],'changed_row_hits':d['changed_row_hits'],
          'relaxed_root_scan':{k:v for k,v in r.items() if k!='first_dispatch_samples'}})
    epochs=json.loads((work/'root-epochs.json').read_text())
    roots=[{'name':r['name'],'fuel':r['fuel'],'dispatch_visits':r['dispatch_visits'],
       'roots':[frame_summary(f) for f in r['root_frames']]} for r in epochs['results']]
    source=json.loads((work/'source-depth.json').read_text())
    return {'scope':__doc__,'origin':origin,'start':64,'halt':254,'working_states':251,'rows':502,
      'baseline_sha256':SHA,'program_sha256':PROGRAM_SHA,
      'mutation_recipes':[{'name':'R252','delete':204,'incoming':[172,1],'replacement':[1,'R',252]},
                          {'name':'L229','delete':204,'incoming':[172,1],'replacement':[1,'L',229]}],
      'prepared_controls':prepared,'literal_blank_controls':blank,'root_epochs':roots,
      'source_depth':{'leaves':source['all_leaf_sites'],'max_consumed':source['max_consumed_path_length'],
        'maximal_paths':source['maximal_paths'],'maintained_controller_gap_contract':40},
      'independent_crosscheck':json.loads((work/'crosscheck-results.json').read_text()),
      'stronger_source_invariant':'At the last loop205 CC2 occurrence within successfulMP par1 restoration, TW=p1+s1 andp1>0. This is original-source reasoning, not a proved mutant invariant.',
      'prepared_pattern_scope':'Observed actualfull-tape pattern TW0,WS=P(1,n),p1=t+1,spare0=k; not universal or proved blankreachable. Other live fields were zero.',
      'off_by_one_history':'Initial diagnostic executed1,000,001 while labeling1M; superseded by exact Python/C++1M full-tape comparison. Correct R2521M q6/head0, old1M+1 q9/head-1 with unchangedones.',
      'nonclaims':['No finitehalt found','No nonhalting theorem from fuelcutoff','No alternativetheory/calculus calibration','No251stateZFC result or lowerbound'],
      'completed_input_artifacts':{n:digest((work/n).read_bytes()) for n in
        ('prepared-controls.json','source-invariant-controls.json','R252-100m.json','L229-100m.json',
         'R252-after-two-roots.json','L229-after-two-roots.json','root-epochs.json','source-depth.json','crosscheck-results.json')},
      'publication_sources':{p.name:digest(p.read_bytes()) for p in files}}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--quick',action='store_true')
    p.add_argument('--cxx',default='g++')
    p.add_argument('--summarize-existing',type=Path,help='Read saved full-run evidence only; explicitly records migrated provenance.')
    a=p.parse_args();assert __debug__,'Assertions required'
    repo=a.repo.resolve();out=a.output.resolve();here=Path(__file__).resolve().parent
    assert out!=repo and repo not in out.parents,'Use externaloutput'
    out.mkdir(parents=True,exist_ok=True)
    files=[here/n for n in ('reproduce.py','prepared.py','root_epochs.py','literal.cpp','relaxed_frames.cpp')]
    raw=(repo/BASELINE).read_bytes();assert digest(raw)==SHA
    assert digest((repo/PROGRAM).read_bytes())==PROGRAM_SHA
    if a.summarize_existing:
        result=summarize(a.summarize_existing.resolve(),files,'Migrated completed scratch runs; portable driver tested separately in quickmode, not a new100M execution.')
        write(out/'summary.json',result);return
    sys.path.insert(0,str(repo/'Computability/BusyBeaver/Research/ZFC'))
    import candidate252_independent_audit as A
    import permutation252_continuations as C
    old=A.read_table(raw)
    assert [(k,v)for k,v in old.items()if v[2]==204]==[((172,1),(1,'R',204))]
    for name,d,target in [('R252','R',252),('L229','L',229)]:
        table={k:v for k,v in old.items()if k[0]!=204};table[172,1]=(1,d,target)
        assert len(table)==502 and len({q for q,b in table})==251
        (out/(name+'.tm')).write_bytes(A.encode(table))
    commands=[]
    def run(command):
        commands.append(command);subprocess.run(command,check=True,stdout=subprocess.DEVNULL)
    for output,cases in [('prepared-controls.json',[(0,1,0),(0,1,1),(0,2,0),(1,1,0),(2,3,2)]),
                          ('source-invariant-controls.json',[(2,1,1),(2,2,0),(5,3,2)])]:
        command=[sys.executable,str(here/'prepared.py'),'--repo',str(repo),'--output',str(out/output)]
        for case in cases:command+=['--case',','.join(map(str,case))]
        run(command)
    for name in ('literal','relaxed_frames'):
        run([a.cxx,'-std=c++20','-O2','-Wall','-Wextra','-o',str(out/name),str(here/(name+'.cpp'))])
    moves=100000 if a.quick else 100000000
    for name in ('R252','L229'):
        run([str(out/'literal'),str(out/(name+'.tm')),str(moves),str(out/(name+'-100m.json'))])
        run([str(out/'relaxed_frames'),str(out/(name+'.tm')),str(moves),str(out/(name+'-relaxed.json'))])
        run([str(out/'relaxed_frames'),str(out/(name+'.tm')),str(moves),str(out/(name+'-after-two-roots.json')),'2'])
    run([sys.executable,str(here/'root_epochs.py'),'--repo',str(repo),'--work',str(out),'--output',str(out/'root-epochs.json')])
    cross=[]
    for name in ('R252','L229'):
        table=A.read_table((out/(name+'.tm')).read_bytes());ones=set();q,h=64,0;count=min(1000000,moves)
        for _ in range(count):
            assert q!=254;w,d,q=table[q,int(h in ones)]
            if w:ones.add(h)
            else:ones.discard(h)
            h+=1 if d=='R'else-1
        cpp=json.loads((out/(name+'-100m.json')).read_text())
        point=next((x for x in cpp['checkpoints']if x['step']==count),cpp['final'])
        assert point['step']==count and(q,h,sorted(ones))==(point['state'],point['head'],point['whole_ones'])
        cross.append({'name':name,'moves':count,'state':q,'head':h,'one_count':len(ones),'full_tape_equal':True,
          'whole_tape_ones_sha256':tape_hash(sorted(ones)),'table_sha256':digest((out/(name+'.tm')).read_bytes())})
    write(out/'crosscheck-results.json',{'results':cross,'scope':'Independent literalPython versusC++ complete tape/state/head at exactcommon stepcount.'})
    nodes=C.read_nodes(repo/PROGRAM);leaves=[]
    def visit(n,path):
        for bit,edge in enumerate(nodes[n]):
            following=path+str(bit)
            if edge.startswith('CN'):visit(int(edge[3:]),following)
            else:leaves.append({'path':following,'edge':edge})
    visit(0,'');maximum=max(len(x['path'])for x in leaves)
    write(out/'source-depth.json',{'all_leaf_sites':len(leaves),'max_consumed_path_length':maximum,
      'maximal_paths':[x for x in leaves if len(x['path'])==maximum]})
    result=summarize(out,files,'Fresh portable quickreplay100k.'if a.quick else'Fresh portable fullreplay100M.')
    result['commands']=commands;write(out/'summary.json',result)
    print(json.dumps({'summary':str(out/'summary.json'),'moves':moves,'status':'pass'}))
if __name__=='__main__':main()
