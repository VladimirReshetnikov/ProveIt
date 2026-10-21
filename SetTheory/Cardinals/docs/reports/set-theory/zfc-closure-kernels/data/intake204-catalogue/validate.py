from pathlib import Path
import hashlib,json,re,subprocess,shutil
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
OUT=Path('/tmp/zfc-intake204-catalogue')
REPORTS=ROOT/'SetTheory/Cardinals/docs/reports'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def capture(argv,name):
 r=subprocess.run(argv,cwd=ROOT,text=True,capture_output=True)
 (OUT/name).write_text(r.stdout+r.stderr)
 assert r.returncode==0,(argv,r.returncode,r.stderr)
 return r.stdout
census=json.loads((OUT/'census.json').read_text())
trees=set(capture(['git','ls-tree','-r','-d','--name-only','HEAD','--','SetTheory/Cardinals/docs/reports'],'tracked-directories.txt').splitlines())
for d in census['directories']: assert str(Path('SetTheory/Cardinals/docs/reports')/d) in trees,d
assert census['report_count']==census['entry_count']==290 and not census['uncovered_tex_pdf']
readme=(REPORTS/'README.md').read_text();tex=(REPORTS/'manifest.tex').read_text()
table={m.group(1):int(m.group(2)) for m in re.finditer(r'^\| \[`([^/]+)/`\].*\| (\d+) \|$',readme,re.M)}
assert table==census['category_counts'],(table,census['category_counts'])
assert '| **Total** | **290** |' in readme
assert 'pdfsubject={Catalogue of 290 independent mathematical research packages}' in tex
assert '167 numbered sources' in tex and 'Sources~165--166' in tex
assert 'Proof\\_Simplification\\_and\\_GC-ZC215\\_2026-10-21.zip' in tex
links=[]
section=readme[readme.index('[Batch 204]'):]
for link in re.findall(r'\[[^\]]*\]\(([^)]+)\)',section):
 p=(REPORTS/link.split('#')[0]).resolve();assert p.exists(),p
 links.append({'link':link,'resolved':str(p.relative_to(ROOT))})
result=json.loads((OUT/'build/result.json').read_text())
assert result['status']=='PASS' and result['source_sha256']==sha(REPORTS/'manifest.tex')
assert result['pdf_sha256']==sha(OUT/'build/manifest.pdf')
log=(OUT/'build/pass2.log').read_text()
issues=[s for s in log.splitlines() if any(t in s for t in ['Warning','Overfull','Underfull','undefined','! '])]
assert not issues,issues
info=capture(['pdfinfo',str(OUT/'build/manifest.pdf')],'pdfinfo.txt')
assert re.search(r'^Pages:\s+140$',info,re.M)
fonts=capture(['pdffonts',str(OUT/'build/manifest.pdf')],'pdffonts.txt')
fontrows=fonts.splitlines()[2:]
assert fontrows and all(re.search(r'\s+yes\s+yes\s+yes\s+\d+\s+\d+\s*$',s) for s in fontrows)
text=(OUT/'build/manifest.txt').read_text()
for t in ['Batch 204 adds Source 167','6177','117,004','ec445a5246','167 numbered','phase five is in progress']:
 assert t in text or t=='6177' and '6,177' in text,t
# The five changed pages were visually reviewed before this installation.
old=sha(REPORTS/'manifest.pdf');shutil.copyfile(OUT/'build/manifest.pdf',REPORTS/'manifest.pdf')
assert sha(REPORTS/'manifest.pdf')==result['pdf_sha256']
owned=['SetTheory/Cardinals/docs/reports/README.md','SetTheory/Cardinals/docs/reports/manifest.tex','SetTheory/Cardinals/docs/reports/manifest.pdf']
capture(['git','diff','--check','--',*owned],'diff-check.txt')
capture(['git','diff','--stat','--',*owned],'diff-stat.txt')
capture(['git','diff','--','SetTheory/Cardinals/docs/reports/README.md','SetTheory/Cardinals/docs/reports/manifest.tex'],'catalogue.diff')
record={'status':'CATALOGUE_UPDATE_VALIDATION_PASS','head_at_validation':capture(['git','rev-parse','HEAD'],'head.txt').strip(),'source167':{'arrival':'05d063acef','placement':'ec445a5246','written_reconciliation':'845040a1fd'},'report_count':290,'source_count':167,'written_sources':'1-164 and167;165-166 pending','tracked_directory_census':True,'uncatalogued_tex_pdf':[],'category_counts':table,'new_links':links,'pdf':{'pages':140,'old_sha256':old,'new_sha256':sha(REPORTS/'manifest.pdf'),'bytes':(REPORTS/'manifest.pdf').stat().st_size,'final_issues':issues,'all_fonts_embedded':True,'visually_reviewed_pages':[1,2,123,139,140]},'changed_catalogue_paths':[{ 'path':p,'sha256':sha(ROOT/p),'bytes':(ROOT/p).stat().st_size} for p in owned],'other_updated_index':'docs/incoming/README.md row204 already included by root in845040a1fd','formal_project_pointer':'Root owns project README and phase5 crosslinks; no overlapping changes here','no_supplied_execution':True,'no_proof_edits':True,'no_git_staging_or_commit':True,'phase5_status':'in progress, no PASS claimed','evidence':{p:sha(OUT/p) for p in ['build/result.json','census.json','catalogue.diff','pdfinfo.txt','pdffonts.txt','diff-check.txt']}}
(OUT/'validation.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['status','report_count','source_count','pdf','changed_catalogue_paths']},indent=2))
