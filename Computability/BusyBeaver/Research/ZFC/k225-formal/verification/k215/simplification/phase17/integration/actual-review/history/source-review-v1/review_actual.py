#!/usr/bin/env python3
"""Owned read-only phase17 actual-result audit; no compiler/imported helper execution.

Run only after terminal PASS and a saved outer exit-zero record. Reads the frozen
selected scope and preserved actual evidence, then writes its own review/copy map.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, re

R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
C=Path('/tmp/k215-phase17-check');B=C/'build-run1'
RUNNER_SHA='322d0a8869f65258722c388b918210f48d98829c7648eef52105f886387282e6'
PLAN_SHA='7b947b62acf1b5e6ecaef1a7036e998a4ce7e3bd0d0e8a38b0dd73af0225ebb5'
SUPERVISOR=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py'
SUPERVISOR_SHA='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LEAN_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
STD={'propext','Classical.choice','Quot.sound'}
ROOTS=['Computability/BusyBeaver/Lean','Logic/FirstOrder/Lean','SetTheory/ZF/Lean','SetTheory/BoundedConsistency/Lean']
BASIS=[(Path('/tmp/k215-phase16-check/primary-run1'),'phase16_primary',195,'3ded969c86762960cda923b7d9aee63953125185a2bb3f64c535d5fe4104462f'),(Path('/tmp/k215-phase16-check/compatibility-run1'),'phase16_compatibility',78,'f16fa4191d1d27864449582d0c40f3ba28eed34a821d53776b75ef2eb6582ddb')]
RAW_SCOPE='Pinned accepted phase16 aggregate, workspace source, object and log; adjacent original raw record additionally checked when present.'

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def profiles(text):return [[n,sorted({a.strip()for a in ax.split(',')if a.strip()})]for n,ax in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",text)]
def strip(text):
    out=[];i=0;depth=0
    while i<len(text):
        if text[i:i+2]=='/-':depth+=1;i+=2
        elif depth and text[i:i+2]=='-/':depth-=1;i+=2
        elif depth:
            if text[i]=='\n':out.append('\n')
            i+=1
        elif text[i:i+2]=='--':
            j=text.find('\n',i);i=len(text)if j<0 else j
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\':i+=2
                elif text[i]=='"':i+=1;break
                else:i+=1
        else:out.append(text[i]);i+=1
    assert depth==0
    return ''.join(out)
def imports(p):return [m for line in re.findall(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)',strip(Path(p).read_text()))for m in line.split()]
def policy(row,rec):
    assert rec['status']=='PASS' and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
    assert sha(rec['log'])==rec['log_sha256'];text=Path(rec['log']).read_text();actual=profiles(text)
    assert 'error:' not in text and 'sorryAx' not in text
    assert all(set(ax)<=STD for _,ax in actual)
    if 'expected_reports'in row:assert actual==row['expected_reports'],(row['module'],'exact profile mismatch')
    else:
        assert [n for n,_ in actual]==row['expected_report_names']
        assert row['allowed_report_axioms']==sorted(STD)
    if row.get('warnings_forbidden'):assert 'warning:' not in text
    return actual

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--outer',type=Path,required=True);parser.add_argument('--out',type=Path,default=Path(__file__).resolve().parent/'review.json');args=parser.parse_args()
    assert sha(C/'build.py')==RUNNER_SHA and sha(C/'plan.json')==PLAN_SHA
    assert sha(SUPERVISOR)==SUPERVISOR_SHA and sha(LEAN)==LEAN_SHA
    freeze=read(C/'freeze.json');assert freeze['files']['build.py']==RUNNER_SHA and freeze['files']['plan.json']==PLAN_SHA
    outer=read(args.outer);assert outer['status']=='PASS_EXIT_ZERO' and outer['exit_code']==0
    assert outer['argv']==['python3','-B',str(C/'build.py'),'--map',str(C/'plan.json'),'--out',str(B)]
    assert outer['stdout_sha256']==sha(C/'build.stdout') and outer['stderr_sha256']==sha(C/'build.stderr')
    assert outer['freeze_sha256']==sha(C/'freeze.json') and (C/'build.stderr').read_bytes()==b''
    plan=read(C/'plan.json');before=read(B/'before.json');result=read(B/'result.json');inventory=read(B/'inventory.json');done=read(B/'completed.json')
    assert result['status']=='PASS' and result['runner_sha256']==before['runner_sha256']==RUNNER_SHA
    assert result['map_sha256']==before['plan_sha256']==PLAN_SHA
    assert result['inventory_sha256']==sha(B/'inventory.json') and result['completed_sha256']==sha(B/'completed.json')
    assert result['source_transitive_reuse_only'] and result['all_source_object_dependency_log_toolchain_inputs_postchecked']
    rows=plan['modules'];selected={r['module']:r for r in rows};assert len(rows)==len(selected)==len(done)==213
    assert inventory=={'modules':rows,'targets':plan['targets'],'external_imports':['Init']}
    assert result['targets']==before['targets']==plan['targets'] and set(done)==set(selected)
    old={};oldrows={};oldorigin={};coverage={};prior_toolchain=None
    for d,origin,count,pin in BASIS:
        assert sha(d/'result.json')==pin;prior=read(d/'result.json');inv=read(d/'inventory.json');completed=read(d/'completed.json')
        assert prior['status']=='PASS' and len(inv['modules'])==len(completed)==count
        assert prior['inventory_sha256']==sha(d/'inventory.json') and prior['completed_sha256']==sha(d/'completed.json')
        toolchain=read(d/'toolchain.json')
        if prior_toolchain is None:prior_toolchain=toolchain
        else:assert prior_toolchain==toolchain
        for row in inv['modules']:
            m=row['module'];rec=completed[m];source=d/'workspace'/(m.replace('.','/')+'.lean');obj=d/'objects'/(m.replace('.','/')+'.olean')
            assert sha(source)==row['source_sha256']==rec['source_sha256'] and imports(source)==row['imports']
            assert sha(obj)==rec['object_sha256'] and sha(rec['log'])==rec['log_sha256']
            assert rec['status']=='PASS' and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
            assert rec['dependencies']=={n:completed[n]['object_sha256']for n in row['imports']if n!='Init'}
            rawpath=Path(rec['log']).with_name('record.json');raw=read(rawpath)if rawpath.is_file()else None
            if raw is not None:
                for key in ['module','source_sha256','dependencies','log_sha256','status']:assert raw[key]==rec[key]
                if 'object_sha256'in raw:assert raw['object_sha256']==rec['object_sha256']
                for key in ['command','exit_code','timed_out']:
                    if key in rec:assert raw[key]==rec[key]
                assert raw['exit_code']==0 and not raw['timed_out'] and raw['command'][:3]==[str(LEAN),'-j1','-M12288']
            coverage[m]={'basis':str(d),'accepted_source':str(source),'log':rec['log'],'raw_record':str(rawpath)if raw is not None else None,'raw_has_object_hash':bool(raw is not None and 'object_sha256'in raw),'scope':RAW_SCOPE}
            if m in old:assert oldrows[m]['source_sha256']==row['source_sha256'] and oldrows[m]['imports']==row['imports'] and old[m]['object_sha256']==rec['object_sha256']
            old[m]=rec;oldrows[m]=row;oldorigin[m]=origin
    assert len(old)==212
    assert coverage==before['historical_raw_coverage']==result['historical_raw_coverage']
    assert sum(v['raw_record']is not None for v in coverage.values())==162
    assert sum(v['raw_record']is None for v in coverage.values())==50
    assert sum(v['raw_record']is not None and not v['raw_has_object_hash']for v in coverage.values())==1
    assert read(B/'toolchain.json')==prior_toolchain
    for key in ['lean','lake','Init.olean','project_toolchain']:
        row=prior_toolchain[key];assert sha(row['path'])==row['sha256']
    changed={m for m,r in selected.items()if m not in old or(r['source_sha256'],r['imports'])!=(oldrows[m]['source_sha256'],oldrows[m]['imports'])}
    forced=set(changed)
    while True:
        more=forced|{m for m,r in selected.items()if set(r['imports'])&forced}
        if more==forced:break
        forced=more
    assert len(changed)==80 and len(forced)==171
    assert sorted(changed)==plan['expected']['changed_sources']==before['changed_sources']==result['changed_sources']
    assert sorted(forced)==plan['expected']['fresh_by_source_transitivity']==before['force_basis_rebuild']==result['force_basis_rebuild']
    visited=set();order=[]
    def visit(m):
        if m=='Init' or m in visited:return
        assert m in selected
        for d in selected[m]['imports']:visit(d)
        visited.add(m);order.append(m)
    for m in plan['targets']:visit(m)
    assert order==[r['module']for r in rows]
    fresh=[];reused=[];clients=[];all_reports={};warning_rows=[];copy=[]
    def addcopy(p,destination):
        p=Path(p);assert p.is_file();copy.append({'source':str(p),'destination':destination,'sha256':sha(p),'bytes':p.stat().st_size})
    for row in rows:
        m=row['module'];rec=done[m];workspace=B/'workspace'/(m.replace('.','/')+'.lean');obj=B/'objects'/(m.replace('.','/')+'.olean')
        assert sha(row['source'])==sha(workspace)==row['source_sha256']==rec['source_sha256'] and imports(workspace)==row['imports']
        assert rec['dependencies']=={d:done[d]['object_sha256']for d in row['imports']if d!='Init'}
        assert sha(obj)==rec['object_sha256'];actual=policy(row,rec);all_reports[m]=actual
        canonical=[R/r/(m.replace('.','/')+'.lean')for r in ROOTS if(R/r/(m.replace('.','/')+'.lean')).is_file()]
        if canonical:assert len(canonical)==1 and canonical[0]==Path(row['source'])
        else:
            clients.append(m);assert row['warnings_forbidden'] and Path(rec['log']).read_text().count('warning:')==0
            if m in old:assert row['source_sha256']==oldrows[m]['source_sha256']
        text=Path(rec['log']).read_text();messages=[line.split('warning:',1)[1].strip()for line in text.splitlines()if'warning:'in line]
        assert len(messages)==rec.get('warnings',len(messages))
        if messages:
            oldtext=Path(old[m]['log']).read_text()if m in old else ''
            warning_rows.append({'module':m,'origin':rec['origin'],'occurrences':len(messages),'messages':messages,'prior_same_module_message_present':[message in oldtext for message in messages],'prior_log_sha256':old[m]['log_sha256']if m in old else None,'log_sha256':rec['log_sha256'],'comparison_scope':'Exact warning headline text, independent of changed paths/line numbers; no claim about explanatory continuation formatting.'})
        if rec['origin']=='candidate_fresh':
            fresh.append(m);assert m in forced and obj.is_file() and not obj.is_symlink()
            rawpath=Path(rec['log']).with_name('record.json');assert read(rawpath)==rec
            assert sha(rec['source'])==row['source_sha256'] and rec['candidate']==row['source']
            assert rec['command']==[str(LEAN),'-j1','-M12288','--root='+str(B/'workspace'),'-o',str(obj),str(workspace)]
            assert rec['timeout_seconds']==(900 if 'KSites215Batch'in m else 120) and rec['memory_mebibytes']==12288
            assert rec['compiler_sha256']==LEAN_SHA and rec['helper_sha256']==SUPERVISOR_SHA
            assert rec['exit_code']==0 and not rec['timed_out']
            assert rec['reports']==actual
            attempt=rawpath.parent;assert sha(attempt/workspace.name)==row['source_sha256']
            addcopy(rawpath,'actual/attempts/'+attempt.name+'/record.json');addcopy(rec['log'],'actual/attempts/'+attempt.name+'/compiler.log')
            addcopy(attempt/workspace.name,'actual/attempts/'+attempt.name+'/'+workspace.name)
        else:
            reused.append(m);assert m not in forced and rec=={**old[m],'origin':oldorigin[m]}
            prior=Path(coverage[m]['basis'])/'objects'/(m.replace('.','/')+'.olean')
            assert obj.is_symlink() and obj.resolve(strict=True)==prior.resolve(strict=True)
        addcopy(workspace,'sources/'+m.replace('.','/')+'.lean')
    assert len(fresh)==171 and set(fresh)==forced and len(reused)==42
    assert result['fresh_modules']==fresh and result['reused_modules']==reused
    assert len(clients)==14 and 'DirectSeed17Api'in clients
    old_primary_clients=set(read(BASIS[0][0]/'inventory.json')['targets'])-{'BusyBeaver.ZFC.KEndpoint215','BusyBeaver.ZFC.KDecoderPrefix215','BusyBeaver.ZFC.PSCCalibration'}
    assert sum(len(all_reports[m])for m in old_primary_clients)==70
    assert sum(len(all_reports[m])for m in ['WFModelCompat12','ZFNativeCompat12'])==10
    assert len(all_reports['BusyBeaver.ZFC.WFTheory'])==5
    new_profiles={m:all_reports[m]for m in selected if m not in old}
    assert new_profiles==result['new_module_actual_profiles'] and sum(len(rs)for rs in new_profiles.values())==5
    audit_reports=[]
    assert len(result['audits'])==len(plan['audits'])==2
    for row,rec in zip(plan['audits'],result['audits']):
        m=row['module'];directory=B/('audit-'+m);source=directory/(m+'.lean');obj=directory/(m+'.olean');raw=directory/'record.json'
        assert rec['module']==m and read(raw)==rec and sha(row['source'])==sha(source)==row['source_sha256']==rec['source_sha256']
        assert rec['command']==[str(LEAN),'-j1','-M12288','--root='+str(directory),'-o',str(obj),str(source)]
        assert rec['dependencies']=={n:r['object_sha256']for n,r in done.items()} and sha(obj)==rec['object_sha256']
        assert rec['timeout_seconds']==120 and rec['memory_mebibytes']==12288 and rec['compiler_sha256']==LEAN_SHA and rec['helper_sha256']==SUPERVISOR_SHA
        assert rec['origin']=='candidate_fresh_audit' and rec['warnings']==0 and rec['exit_code']==0 and not rec['timed_out']
        actual=policy(row,rec);assert rec['reports']==actual;audit_reports.extend(actual)
        for p in [raw,Path(rec['log']),source]:addcopy(p,'actual/audit-'+m+'/'+p.name)
    assert len(audit_reports)==10
    # Independently enumerate only the finite literal program table's decoder leaves.
    # This is static source binding, not TM execution or a rerun of a supplied generator.
    program=Path(selected['BusyBeaver.ZFC.KSource215Program']['source']).read_text();nodes={}
    edge=r'\(?\.(node|inc|decnz|brk|cont|halt)(?:\s+(\d+))?\)?'
    for match in re.finditer(r'(?m)^\s*\| (\d+) => \('+edge+r', '+edge+r'\)\s*$',program):
        n,a,ai,b,bi=match.groups();assert int(n)not in nodes;nodes[int(n)]=[(a,int(ai)if ai else 0),(b,int(bi)if bi else 0)]
    assert set(nodes)==set(range(179)) and re.search(r'def p215 : Program := ⟨p215Nodes, 178, 179⟩',program)
    assert 'def t215 : Tree := ptree p215'in program and 'theorem t215_eq : ptree p215 = t215 := by rfl'in program
    leafcodes={'inc':'CI','decnz':'CD','brk':'CB','cont':'CC','halt':'CH'};leaves=[]
    def walk(n,fuel,prefix):
        assert fuel>0
        for bit,(kind,arg)in zip('01',nodes[n]):
            path=prefix+bit
            if kind=='node':walk(arg,fuel-1,path)
            else:leaves.append([path,leafcodes[kind],arg])
    walk(178,180,'')
    original=R/'Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json';assert leaves==read(original) and len(leaves)==4751
    kinds=Counter(row[1]for row in leaves);assert dict(kinds)=={'CD':1425,'CB':98,'CI':1900,'CC':1327,'CH':1}
    assert sum(2 if row[1]=='CD'else 1 for row in leaves)==6176
    blocks={};site_modules=['BusyBeaver.ZFC.KSites215Batch'+str(i).zfill(3)for i in range(9)]
    for m in site_modules:
        assert m in fresh and selected[m]['source_sha256']==oldrows[m]['source_sha256']
        text=Path(selected[m]['source']).read_text();pattern=r'theorem block_(\d+)\s*:\s*allSites \(KSim.checkEdge tm215\) \[([^]]*)\]\s*\(descend KSource215.t215 \[([^]]*)\]\) = true := by\s*exact KFastSites215.allSites_of_fast \(by decide \+kernel\)'
        matches=list(re.finditer(pattern,text));assert len(matches)==len(re.findall(r'(?m)^theorem block_',text))
        for match in matches:
            num,rev,forward=match.groups();num=int(num);assert num not in blocks
            bits=lambda s:[x.strip()for x in s.split(',')if x.strip()]
            assert bits(rev)==list(reversed(bits(forward))) and set(bits(forward))<={'true','false'}
            blocks[num]=''.join('1'if x=='true'else'0'for x in bits(forward))
    assert set(blocks)==set(range(105))
    for prefix in blocks.values():assert any(row[0].startswith(prefix)for row in leaves)
    assert all(sum(path.startswith(prefix)for prefix in blocks.values())==1 for path,_,_ in leaves)
    root=Path(selected['BusyBeaver.ZFC.KSites215']['source']).read_text();assert selected['BusyBeaver.ZFC.KSites215']['source_sha256']==oldrows['BusyBeaver.ZFC.KSites215']['source_sha256']
    assert sorted(map(int,re.findall(r'\bblock_(\d+)\b',root)))==list(range(105))
    assert 'theorem all_sites : allSites (KSim.checkEdge tm215) [] KSource215.t215 = true :='in root
    assert 'KSim.covered_of_allSites tm215 KSource215.p215 KSource215.t215 KSource215.t215_eq all_sites'in root
    endpoint=set()
    def ep(m):
        if m=='Init'or m in endpoint:return
        endpoint.add(m)
        for d in selected[m]['imports']:ep(d)
    ep('BusyBeaver.ZFC.KEndpoint215')
    assert len(endpoint)==174 and sum(Path(selected[m]['source']).stat().st_size for m in endpoint)==1749188
    assert len(plan['present_inputs'])==54 and len(plan['absent_inputs'])==7
    for p,h in plan['present_inputs'].items():assert sha(p)==h and before['inputs'][p]==h
    for p,h in before['inputs'].items():assert sha(p)==h,p
    assert before['absent_inputs']==plan['absent_inputs']
    for p in plan['absent_inputs']:assert not Path(p).exists() and not Path(p).is_symlink()
    for m in plan['retired_modules']:
        assert m not in selected;p=B/'objects'/(m.replace('.','/')+'.olean');assert not p.exists() and not p.is_symlink()
    stdout=(C/'build.stdout').read_text();assert re.findall(r'(?m)^CHECK (\S+)$',stdout)==fresh
    assert re.findall(r'(?m)^REUSE (\S+) ',stdout)==reused and re.findall(r'(?m)^AUDIT (\S+)$',stdout)==[r['module']for r in plan['audits']]
    assert stdout.rstrip().endswith('COMPLETE 213 2 audits') and not re.search(r'(?m)^FAIL\b',stdout)
    for p in [C/'build.py',C/'plan.json',C/'freeze.json',args.outer,C/'build.stdout',C/'build.stderr',B/'result.json',B/'before.json',B/'inventory.json',B/'completed.json',B/'toolchain.json']:
        addcopy(p,'actual/'+p.name)
    destinations=[r['destination']for r in copy];assert len(destinations)==len(set(destinations))
    review={'status':'PASS_READ_ONLY_ACTUAL_EVIDENCE_REVIEW','runner_sha256':RUNNER_SHA,'plan_sha256':PLAN_SHA,'outer_sha256':sha(args.outer),'result_sha256':sha(B/'result.json'),'provider_count':213,'project_modules':199,'typed_clients':14,'changed_sources':80,'fresh_providers':171,'source_transitive_reuses':42,'endpoint_project_modules':174,'endpoint_source_bytes':1749188,'all_old_primary_client_reports':70,'compatibility_client_reports':10,'WFTheory_reports':5,'fresh_endpoint_audit_reports':audit_reports,'new_exact_profiles':new_profiles,'site_batches':9,'site_blocks':105,'site_leaves':4751,'site_outcomes':6176,'site_edge_kinds':dict(kinds),'site_scope':'Fresh kernel checks of all nine batches plus root coverage; original pinned site list exactly equals statically enumerated literal program decoder leaves.','historical_raw_present':162,'historical_raw_absent_inherited':50,'historical_raw_missing_object_hash':1,'historical_raw_scope':RAW_SCOPE,'additional_pins_postchecked':54,'absences_postchecked':7,'warning_occurrences':sum(r['occurrences']for r in warning_rows),'fresh_warning_occurrences':sum(r['occurrences']for r in warning_rows if r['origin']=='candidate_fresh'),'all_fresh_warning_headlines_preexisted':all(all(r['prior_same_module_message_present'])for r in warning_rows if r['origin']=='candidate_fresh'),'warnings':warning_rows,'client_and_audit_warnings':0,'copy_plan_files':len(copy),'objects_copied':False,'helper_sha256':sha(__file__),'scope':'Frozen combined215 closure and named compatibility/API/macro roots only; no variant217–225 full-stack claim.'}
    save(args.out,review);save(args.out.with_name('publication-copy-plan.json'),{'status':'DRAFT_COPY_PLAN_NO_MUTATION','files':copy,'scope':'Selected actual sources, fresh invocation source/log/record evidence, audits and small metadata; no object files, supplied-code execution, or new archive reader.'});print(json.dumps(review,indent=2))

if __name__=='__main__':main()
