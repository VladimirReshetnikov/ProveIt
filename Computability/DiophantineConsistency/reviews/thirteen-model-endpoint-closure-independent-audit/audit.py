#!/usr/bin/env python3
"""Independent source/frontier arithmetic and read-only provider guard review."""
import hashlib,importlib.util,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-endpoint-closure'
BASEMAN=Path('/tmp/ipra-ordinary12-coexistence-source-03/manifest.json')
HIST=Path('/tmp/ipra-aq29-fresh-source-closure-v2/manifest.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    prefix=PKG.relative_to(ROOT).as_posix()+'/'
    names=subprocess.run(['git','ls-tree','-r','--name-only','435062d125','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
    need(len(names)==11,'source inventory')
    for name in names:
        p=ROOT/name;b=subprocess.run(['git','show','435062d125:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+name)
    survey=json.loads((PKG/'source-manifest.json').read_bytes());comp=json.loads((PKG/'historical-comparison.json').read_bytes());plan=json.loads((PKG/'frontier-plan.json').read_bytes());objs=json.loads((PKG/'provider-object-comparison.json').read_bytes());base=json.loads(BASEMAN.read_bytes());hist=json.loads(HIST.read_bytes())
    need(sha(BASEMAN)==comp['base_manifest_sha256'] and sha(HIST)==comp['historical_manifest_sha256'] and sha(PKG/'source-manifest.json')==comp['source_survey_sha256'],'manifest pins')
    rows=dict(base['sources']);rows.update(survey['sources']);selected=set(survey['sources']);todo=list(survey['direct_parent_boundary'])
    while todo:
        n=todo.pop()
        if n not in selected:
            need(n in base['sources'],'boundary source '+n);selected.add(n);todo.extend(x for x in base['sources'][n]['imports'] if x in base['sources'])
    old=set(hist['sources']);new=selected-old;changed={n for n in selected&old if rows[n]['sha256']!=hist['sources'][n]['sha256']}
    changeddeps={n for n in selected&old if rows[n]['imports']!=hist['sources'][n]['imports']}
    dirty=set(new)|changed
    while True:
        extra={n for n in selected-dirty if any(x in dirty for x in rows[n]['imports'])}
        if not extra:break
        dirty.update(extra)
    clean=selected-dirty
    need((len(selected),len(new),len(changed),len(changeddeps),len(dirty),len(clean))==(1145,49,15,0,338,807),'independent closure counts')
    need(set(comp['new_modules'])==new and set(comp['changed_modules'])==changed and set(comp['dirty_reverse_closure'])==dirty,'comparison sets')
    need(set(plan['rebuild_order'])==dirty and set(plan['reusable_seeds'])==clean and set(plan['all_selected_source_hashes'])==selected,'frontier sets')
    order=[n for n in base['order'] if n in selected]+[n for n in survey['order'] if n in selected];pos={n:i for i,n in enumerate(order)}
    need(len(pos)==len(order)==len(selected) and all(pos[d]<pos[n] for n in order for d in rows[n]['imports'] if d in selected),'topology')
    need(all(plan['all_selected_source_hashes'][n]==rows[n]['sha256']==sha(ROOT/rows[n]['workspace_path']) for n in selected),'workspace source hashes')
    need(len(plan['rebuild_external_guards'])==27,'rebuild external count')
    for side in ('author','peer'):
        need(plan['checks'][side]['seed_count']==807 and plan['checks'][side]['direct_and_output_guard_count']==9080 and len(plan['direct_and_seed_output_guards'][side])==9080,'seed guard count')
    need(objs['per_side_overlap']==104 and objs['per_side_differing']==6 and len(objs['different_modules'])==6,'provider difference count')
    spec=importlib.util.spec_from_file_location('survey',PKG/'survey.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    for n in selected:
        path=ROOT/rows[n]['workspace_path'];text=mod.strip_comments(path.read_text(),path)
        need(not any(re.match(r'^\s*(?:public|private|protected|meta|unsafe)\s+import\b',line) for line in text.splitlines()),'modifier import '+n)
        need(mod.imports(path.read_bytes(),path)==rows[n]['imports'],'declared imports '+n)
    outputs=[]
    for script,args in (('survey.py',[]),('compare_historical.py',['--check']),('compare_provider_objects.py',['--check']),('frontier_plan.py',['--check'])):
        p=subprocess.run([sys.executable,'-I','-S',str(PKG/script),*args],capture_output=True,text=True,timeout=240)
        need(p.returncode==0 and not p.stderr,'check failed '+script+' '+p.stderr);outputs.append({'script':script,'exit':p.returncode,'stdout':p.stdout.strip()})
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_ENDPOINT_CLOSURE_AUDIT','source_commit':'435062d125','selected':len(selected),'new':len(new),'changed':len(changed),'changed_import_lists':len(changeddeps),'dirty':len(dirty),'reusable':len(clean),'historical_objects_checked_per_side':1210,'provider_overlap':104,'provider_mismatches':objs['different_modules'],'seed_direct_and_output_guards_per_side':9080,'rebuild_external_modules':len(plan['rebuild_external_guards']),'checks':outputs,'scope':'Source-declared candidate frontier and point-in-time object/companion checks; not a Lean build, compiled endpoint-binding draft, complete axiom inventory, or iPRA proof.'},indent=2))
if __name__=='__main__':main()
