#!/usr/bin/env python3
"""Read-only, lexical Lean import and bounded candidate-object audit; does not run Lean."""
from pathlib import Path
import hashlib,json,re,collections
HERE=Path(__file__).resolve().parent
TASK=HERE.parents[1]
DRAFT=TASK/'research/adaptive87-four-square-current88-model-draft'
CUSTOM={name:DRAFT/(name+'.lean.src') for name in ['AdaptiveFourSquare88Graph','FourUnitGeneric','FourSquare88Model']}
ROOTS={'ha87_historical':'/tmp/ha87-full-transitive-p3xt6wra/lib',
       'current14_fresh_base':'/tmp/current14-standard-fresh-build-20261104/lib',
       'foundation_package':'/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'}

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
# The import syntax in the scanned prefix is deliberately narrow.  Unknown
# nonblank syntax terminates a header rather than claiming comprehensive parsing.
def imports(path):
    s=path.read_text();out=[];i=0;depth=0;clean=[]
    while i<len(s):
        if s.startswith('/-',i): depth+=1;i+=2
        elif depth and s.startswith('-/',i): depth-=1;i+=2
        elif depth: i+=1
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        else: clean.append(s[i]);i+=1
    assert depth==0, path
    for line in ''.join(clean).splitlines():
        line=line.strip()
        if not line: continue
        m=re.fullmatch(r'(?:public\s+)?import\s+([\w.]+(?:\s+[\w.]+)*)',line)
        if m: out.extend(m.group(1).split());continue
        if line in ('module','prelude'):continue
        break
    return out

def src(name):
    if name in CUSTOM:return CUSTOM[name]
    if name.startswith('DiophantineConsistency.'):
        return TASK/'Lean'/Path(*name.split('.')).with_suffix('.lean')
    return None

q=collections.deque(['FourSquare88Model']);seen={};external=set();missing=set()
while q:
    name=q.popleft()
    if name in seen or name in external or name in missing:continue
    p=src(name)
    if p is None:external.add(name);continue
    if not p.is_file():missing.add(name);continue
    edges=imports(p)
    seen[name]={'source':str(p.relative_to(TASK)),'sha256':digest(p),'imports':edges}
    q.extend(edges)
assert len(seen)>=3 and set(CUSTOM)<=set(seen)
assert 'DiophantineConsistency.ModelArithmetic' in seen['FourSquare88Model']['imports']
assert 'DiophantineConsistency.ModelDifferenceRing' in seen['DiophantineConsistency.ModelArithmetic']['imports']
project=set(seen)-set(CUSTOM)
providers={}
statuses={}
snapshots={'ha87_historical':Path('/tmp/ha87-frozen-full-e_jgyudl/tree/Computability/DiophantineConsistency/Lean'),
           'current14_fresh_base':Path('/tmp/current14-standard-fresh-source-20261104/src')}
for label,root_string in ROOTS.items():
    root=Path(root_string)
    counts=collections.Counter();direct={};collisions={}; statuses[label]={}; source_comparison=collections.Counter();source_different=[]
    for name in sorted(project):
        p=root/Path(*name.split('.')).with_suffix('.olean')
        state='file' if p.is_file() else ('dangling_symlink' if p.is_symlink() else 'absent')
        counts[state]+=1; statuses[label][name]=state
        if state=='file' and label in snapshots:
            snap=snapshots[label]/Path(*name.split('.')).with_suffix('.lean')
            kind='same' if snap.is_file() and digest(snap)==seen[name]['sha256'] else ('different' if snap.is_file() else 'snapshot_source_absent')
            source_comparison[kind]+=1
            if kind!='same':source_different.append(name)
    for name in sorted(set(sum([seen[n]['imports'] for n in CUSTOM],[]))-set(CUSTOM)):
        p=root/Path(*name.split('.')).with_suffix('.olean')
        direct[name]={'state':'file' if p.is_file() else ('dangling_symlink' if p.is_symlink() else 'absent')}
        if p.is_file():direct[name]['sha256']=digest(p)
    for name in CUSTOM:
        p=root/(name+'.olean');collisions[name]={'present':p.exists(),'symlink':p.is_symlink()}
    providers[label]={'root':root_string,'root_is_directory':root.is_dir(),'project_module_status_counts':dict(sorted(counts.items())),
                      'direct_objects':direct,'draft_name_collisions':collisions,'current_vs_snapshot_source_for_present_objects':dict(sorted(source_comparison.items())),'current_vs_snapshot_source_changed_or_missing':source_different}
factor_name='DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011'
old_factor=snapshots['ha87_historical']/Path(*factor_name.split('.')).with_suffix('.lean')
new_factor=src(factor_name)
factor_visibility={}
for lemma in ('first_bad','main_bad','strong_bad','aux_bad'):
    pattern=r'^private theorem '+lemma+r'\b'
    old=bool(re.search(pattern,old_factor.read_text(),re.M))
    new=bool(re.search(r'^theorem '+lemma+r'\b',new_factor.read_text(),re.M))
    used=bool(re.search(r'\b'+lemma+r'\b',CUSTOM['FourUnitGeneric'].read_text()))
    assert old and new and used, lemma
    factor_visibility[lemma]={'historical_private':old,'current_public':new,'generic_mentions':used}
union_absent=sorted(n for n in project if all(statuses[k][n]!='file' for k in ('ha87_historical','current14_fresh_base')))
overlap=sorted(n for n in project if all(statuses[k][n]=='file' for k in ('ha87_historical','current14_fresh_base')))
res={'schema':1,'method':'lexical initial import prefixes of three selected draft sources and reachable existing DiophantineConsistency sources under Lean/; explicit nonproject frontier',
     'selected_modules':{n:seen[n] for n in sorted(CUSTOM)},'project_source_count':len(project),'project_sources':{n:seen[n] for n in sorted(project)},
     'unresolved_project_sources_under_Lean':sorted(missing),'external_import_frontier':sorted(external),'provider_observations':providers,'factor_unit_visibility':{'historical_source_sha256':digest(old_factor),'current_source_sha256':digest(new_factor),'declarations':factor_visibility},'absent_from_both_project_roots':union_absent,'present_in_both_project_roots':overlap,
     'limitations':['No Lean run, no object/source authentication, no elaboration or build readiness claim.',
       'Project imports are scanned only below Lean/DiophantineConsistency, not package or external transitive closure.',
       'Object presence is not compatibility, source freshness, or provenance; candidate roots are not selected for a build.',
       'Snapshot source equality is not authentication of object bytes, transitive providers, or object compilation inputs.',
       'Import-prefix parsing is lexical and cannot establish elaboration-generated dependencies.']}
print(json.dumps(res,sort_keys=True,indent=2))
