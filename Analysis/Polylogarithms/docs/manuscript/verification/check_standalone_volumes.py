"""Build each volume in isolation, using committed companion label indices."""
from pathlib import Path
import hashlib,json,os,subprocess,time
import fitz

B=Path(__file__).resolve().parents[1];V=B/'verification'
plan=json.loads((V/'volume-plan.json').read_text(encoding='utf-8'))
root=V/'.scratch-volumes'/('standalone-'+str(time.time_ns()))
root.mkdir(parents=True)
env=dict(os.environ);env['TEXINPUTS']=os.pathsep
records=[]
for volume in plan:
    stem=volume['stem'];out=root/str(volume['number']);out.mkdir()
    passes=[]
    for number in range(1,4):
        p=subprocess.run(['lualatex','-interaction=nonstopmode','-halt-on-error',
            '-output-directory='+out.resolve().as_posix(),'volumes/'+stem+'.tex'],
            cwd=B,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
            text=True,encoding='utf-8',errors='replace')
        (out/f'pass-{number}.txt').write_text(p.stdout,encoding='utf-8')
        if p.returncode:raise SystemExit(p.returncode)
        passes.append(dict(number=number,exit_code=p.returncode))
    log=(out/(stem+'.log')).read_text(encoding='utf-8',errors='replace')
    issues=[s for s in log.splitlines() if any(k in s for k in
        ['undefined','multiply defined','Overfull','Missing character','Rerun to get','Label(s) may have changed'])]
    primary=fitz.open(B/'volumes'/(stem+'.pdf'));standalone=fitz.open(out/(stem+'.pdf'))
    primary_text='\n'.join(p.get_text() for p in primary)
    standalone_text='\n'.join(p.get_text() for p in standalone)
    def targets(doc):
        return sorted((n,doc.xref_get_key(link['xref'],'A/F'),doc.xref_get_key(link['xref'],'A/D'))
            for n,page in enumerate(doc) for link in page.get_links() if link.get('file'))
    equal=primary_text==standalone_text and targets(primary)==targets(standalone)
    record=dict(number=volume['number'],passes=passes,issues=issues,
        page_count=len(standalone),text_matches_primary=primary_text==standalone_text,
        PDF_link_targets_match=targets(primary)==targets(standalone),
        text_sha256=hashlib.sha256(standalone_text.encode()).hexdigest(),passed=not issues and equal)
    records.append(record)
    print('Isolated volume',volume['number'],'PASS' if record['passed'] else 'FAIL',flush=True)
    if not record['passed']:raise SystemExit(1)
result=dict(passed=all(x['passed'] for x in records),volumes=records,
    scope='Each source compiled three times in an empty isolated output folder, with no companion aux search path. Committed label indices produce identical page text and PDF link targets.')
(V/'volume-standalone-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('All four volume sources compile independently.')
