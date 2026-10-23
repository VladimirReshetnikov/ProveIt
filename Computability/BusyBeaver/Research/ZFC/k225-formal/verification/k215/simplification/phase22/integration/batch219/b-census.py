"""Owned inert-source import/body census. Runs no supplied code or prover."""
from pathlib import Path
import subprocess, tomllib, re, json, hashlib
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
OUT=Path('/tmp/k215-batch219-review-b')
IN=OUT/'inputs'
BASE='cbf94cb552a3b49509e0eee80e7455d4eb5974c6'
libs=tomllib.loads((ROOT/'lakefile.toml').read_text())['lean_lib']
roots={x['name']:x.get('srcDir','.') for x in libs}

def clean(text):
    result=[];i=0;depth=0;quote=False
    while i<len(text):
        if depth:
            if text[i:i+2]=='/-':depth+=1;i+=2
            elif text[i:i+2]=='-/':depth-=1;i+=2
            else:
                if text[i]=='\n':result.append('\n')
                i+=1
        elif quote:
            if text[i]=='\\':i+=2
            elif text[i]=='"':quote=False;i+=1
            else:
                if text[i]=='\n':result.append('\n')
                i+=1
        elif text[i:i+2]=='/-':depth=1;i+=2
        elif text[i:i+2]=='--':
            j=text.find('\n',i);i=len(text) if j<0 else j
        elif text[i]=='"':quote=True;i+=1
        else:result.append(text[i]);i+=1
    return ''.join(result)

def path_of(module):
    root=module.split('.')[0]
    if root in ['Init','Std','Lean','Mathlib']:return None
    assert root in roots,(module,'unknown root')
    return Path(roots[root])/Path(module.replace('.','/')+'.lean')

def imports(data):
    text=clean(data.decode())
    return [name for line in re.findall(r'^(?:public |meta )?import (.*)$',text,re.M)
            for name in line.split()]

cache={}
def get(module,base=False):
    key=(module,base)
    if key in cache:return cache[key]
    path=path_of(module)
    if path is None:return None
    if base:data=subprocess.check_output(['git','show',BASE+':'+str(path)],cwd=ROOT)
    else:data=(ROOT/path).read_bytes()
    cache[key]=(str(path),data)
    return cache[key]

def overlay(folder):
    return {'.'.join(p.relative_to(folder).with_suffix('').parts):(str(p),p.read_bytes())
            for p in folder.rglob('*.lean')}

native=overlay(IN/'consolidation-plan/lean-native/overlay')
spine=overlay(IN/'proof-spine/lean/candidate')
combined=dict(spine)
for module in ['BusyBeaver.ZFC.KQ1ReplacementNative','BusyBeaver.ZFC.KQ1ZF']:
    combined[module]=native[module]

def census(label,overrides=None,base=False):
    overrides=overrides or {}; selected={}; visiting=set()
    def visit(m):
        if m in selected:return
        assert m not in visiting,('cycle',label,m)
        visiting.add(m)
        value=overrides.get(m) or get(m,base)
        if value is None:visiting.remove(m);return
        path,data=value
        deps=imports(data)
        for dep in deps:visit(dep)
        selected[m]={'path':path,'sha256':hashlib.sha256(data).hexdigest(),
                     'bytes':len(data),'lines':data.count(b'\n'),'imports':deps}
        visiting.remove(m)
    visit('BusyBeaver.ZFC.KEndpoint215')
    return {'label':label,'project_modules':len(selected),
            'bytes':sum(x['bytes'] for x in selected.values()),
            'lines':sum(x['lines'] for x in selected.values()),'sources':selected}

censuses=[census('packet baseline',base=True),census('current phase22 v2'),
          census('current + native',native),census('current + spine',spine),
          census('current + spine + native merged',combined)]
base=censuses[1]
for row in censuses[2:]:
    row['delta_vs_current']={k:row[k]-base[k] for k in ['project_modules','bytes','lines']}
    row['removed_vs_current']=sorted(set(base['sources'])-set(row['sources']))
    row['added_vs_current']=sorted(set(row['sources'])-set(base['sources']))
for name,ov in [('native',native),('spine',spine),('combined',combined)]:
    oldbytes=oldlines=newbytes=newlines=0
    for module,(_,data) in ov.items():
        path=path_of(module)
        old=(ROOT/path).read_bytes() if (ROOT/path).exists() else b''
        oldbytes+=len(old);oldlines+=old.count(b'\n');newbytes+=len(data);newlines+=data.count(b'\n')
    for row in censuses:
        if row['label']=={'native':'current + native','spine':'current + spine','combined':'current + spine + native merged'}[name]:
            row['total_affected_maintenance_delta']={'bytes':newbytes-oldbytes,'lines':newlines-oldlines}

# Check declarations really are unchanged through core/facade moves.
movechecks=[]
for module in ['SingletonInfinity','FiniteSets','InductiveAttempts','WellFoundedPart']:
    original=(ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'/f'{module}.lean').read_text()
    core=(IN/'proof-spine/lean/candidate/BusyBeaver/ZFC'/f'{module}Core.lean').read_text()
    wrapper=(IN/'proof-spine/lean/candidate/BusyBeaver/ZFC'/f'{module}.lean').read_text()
    boundary={'SingletonInfinity':'theorem quotientBase','FiniteSets':'theorem quotientBase',
              'InductiveAttempts':'theorem quotientFiniteBase',
              'WellFoundedPart':'/-- The actual quotient'}[module]
    if module=='WellFoundedPart':
        # Inspect the first quotient declaration; adjacent documentation stays with facade.
        boundary='theorem quotient_wf_closure'
    i=original.index(boundary)
    firstdecl=re.search(r'^(?:(?:noncomputable|private|protected) )*(?:def|abbrev|theorem|structure|inductive) ',original,re.M).start()
    generic=original[firstdecl:i].rstrip()
    if module=='WellFoundedPart':
        # Exact proof block, excluding only the comment preceding the quotient tail.
        generic=original[firstdecl:original.rfind('/--',firstdecl,i)].rstrip()
    else:
        # Original quotient comment (if any) must not be mistaken for a generic declaration.
        doc=original.rfind('/--',firstdecl,i)
        end=original.rfind('\n\n',firstdecl,i)
        if doc>end:generic=original[firstdecl:doc].rstrip()
    generic_same=generic in core
    tail=original[i:original.index('\nend ',i)].rstrip()
    tail_same=tail in wrapper
    movechecks.append({'module':module,'generic_body_exact_substring':generic_same,'quotient_tail_exact_substring':tail_same})

# Record exact phase22 map and compare normalization bytes to adopted source.
specpath=Path('/tmp/k215-phase22-check-v2/source-spec-v2.json')
specdata=specpath.read_bytes();spec=json.loads(specdata)
phase22=[]
for source in spec['sources']:
    data=Path(source['canonical']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==source['candidate']['sha256']
    phase22.append({'module':source['module'],'candidate_sha256':source['candidate']['sha256']})
report={'scope':'source-only; no supplied scripts/proofs/TeX or compiler executed',
        'packet_commit':'56b37bde8b064d852154ad8478d58ec9ab5375d6',
        'baseline_commit':BASE,'censuses':censuses,'source_move_checks':movechecks,
        'phase22_spec_path':str(specpath),'phase22_spec_sha256':hashlib.sha256(specdata).hexdigest(),
        'phase22_sources':phase22,
        'checked_interfaces_normalization_matches_current':
            (ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleAbs.lean').read_bytes()==
            (IN/'checked-interfaces/lean-normalization/proposed/BusyBeaver/ZFC/ConstructibleAbs.lean').read_bytes(),
        'merge_rule':'Use all twelve spine sources; add native KQ1ReplacementNative and take native KQ1ZF. Do not overwrite spine InductiveAttemptsCore with native old-import core.'}
(OUT/'owned-census.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'censuses':[{k:v for k,v in x.items() if k!='sources'} for x in censuses],
                  'source_move_checks':movechecks,'normalization_already_adopted':report['checked_interfaces_normalization_matches_current']},indent=2))
