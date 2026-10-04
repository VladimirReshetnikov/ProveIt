#!/usr/bin/env python3
"""Fresh immutable publication metadata; no report helpers imported or executed."""
from pathlib import Path
import argparse, hashlib, json, posixpath, re, subprocess

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
COMMIT='ddb36da6c510b9ace2cc15475bd553a32a3cfadf'
BASE='Algebra/SurrealNumbers/docs/foundations-and-computation/'
DSN=BASE+'definable-surreals-and-omnific-integers/article.tex'
FOUND=BASE+'foundations/article.tex'
HSET=BASE+'birthday-cutoffs-and-hereditary-sets/article.tex'
OUT=Path('/tmp/review_new_reciprocal_ddb36da6c.json')
CACHE={}

def require(ok,msg):
    if not ok: raise ValueError(msg)
def sha(b): return hashlib.sha256(b).hexdigest()
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT)
def content(c,p):
    if (c,p) not in CACHE: CACHE[c,p]=git('show',c+':'+p)
    return CACHE[c,p]
def pin(c,p):
    b=content(c,p)
    return {'commit':c,'path':p,'blob':git('rev-parse',c+':'+p).decode().strip(),'bytes':len(b),'sha256':sha(b)}
def readspan(c,p,a,z,scope):
    b=content(c,p); lines=b.splitlines(keepends=True)
    require(1<=a<=z<=len(lines),'span bounds')
    s=b''.join(lines[a-1:z])
    return {**pin(c,p),'start_line':a,'end_line':z,'span_bytes':len(s),'span_sha256':sha(s),'normalization':'raw Git bytes, line endings preserved','scope':scope}
def labels(b): return re.findall(r'\\label\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}',b.decode())
def bibs(b): return re.findall(r'\\bibitem\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}',b.decode())

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--expect',type=Path);args=ap.parse_args()
    parent=git('rev-parse',COMMIT+'^').decode().strip()
    paths=git('diff-tree','--no-commit-id','--name-only','-r',COMMIT).decode().splitlines()
    require(len(paths)==6,'six changed paths')
    files=[];reads=[];added_records=[]
    for p in paths:
        old,new=content(parent,p),content(COMMIT,p)
        d=git('diff','--no-ext-diff','--no-textconv','--unified=3',parent,COMMIT,'--',p)
        f={'path':p,'before':pin(parent,p),'after':pin(COMMIT,p),'diff_sha256':sha(d),'diff_bytes':len(d),
           'coverage':'PDF bytes only; not viewed or built' if p.endswith('.pdf') else 'entire textual diff read, including both sides of hunk context'}
        if not p.endswith('.pdf'):
            dl=d.decode().splitlines();hunks=[];plus=minus=0;nline=None
            for line in dl:
                m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',line)
                if m:
                    a,an,z,zn=int(m[1]),int(m[2] or 1),int(m[3]),int(m[4] or 1)
                    h={'before_start':a,'before_count':an,'after_start':z,'after_count':zn};hunks.append(h);nline=z
                    if an:reads.append(readspan(parent,p,a,a+an-1,'full before-side diff hunk read'))
                    if zn:reads.append(readspan(COMMIT,p,z,z+zn-1,'full after-side diff hunk read'))
                elif line.startswith('+') and not line.startswith('+++'):
                    plus+=1;added_records.append({'path':p,'line':nline,'text':line[1:]});nline+=1
                elif line.startswith('-') and not line.startswith('---'):minus+=1
                elif line.startswith(' ') and nline is not None:nline+=1
            f.update({'hunks':hunks,'added_lines':plus,'removed_lines':minus,'diff_lines':len(dl)})
        if p.endswith('.tex'):
            lo,ln=labels(old),labels(new);bo,bn=bibs(old),bibs(new)
            require(lo==ln,'unchanged labels '+p);require(bo==bn,'unchanged bibliography '+p)
            f['unchanged_label_list']=ln;f['unchanged_bibliography_keys']=bn
        files.append(f)
    extra={DSN:[(10245,10357),(11098,11203)],FOUND:[(1150,1220),(3133,3200)],
           HSET:[(8620,8728),(8853,8915),(9108,9163),(9374,9417),(9542,9646),(10114,10170),(10625,10670),(11124,11173)]}
    for p,sp in extra.items():
        for a,z in sp:reads.append(readspan(COMMIT,p,a,z,'selected cited mathematical/status interface read'))
    reads.append(readspan(COMMIT,DSN,111,111,'writenote environment definition; no theorem counter operation'))
    agents='Algebra/SurrealNumbers/AGENTS.md'
    reads.append(readspan(COMMIT,agents,1,len(content(COMMIT,agents).splitlines()),'full applicable instructions read'))
    reads.append(readspan(COMMIT,'docs/incoming/README.md',421,442,'incoming rebuild/retention standing rules read'))
    index={};index_files=[]
    for p in [DSN,FOUND,HSET]:
        b=content(COMMIT,p);index_files.append(pin(COMMIT,p))
        for n,line in enumerate(b.decode().splitlines(),1):
            for lab in labels(line.encode()):index.setdefault(lab,[]).append({'path':p,'line':n})
    routes=[];citations=[];links=[]
    for r in added_records:
        for lab in re.findall(r'\b(?:hset|dsn|found):[A-Za-z0-9:_-]+',r['text']):
            matches=index.get(lab,[]);require(len(matches)==1,'unique literal added-label target '+lab)
            routes.append({'source_path':r['path'],'source_line':r['line'],'label':lab,'matches':matches})
        if r['path'].endswith('.tex'):
            for m in re.finditer(r'\\cite\w*\*?(?:\[[^\]]*\])*\{([^}]+)\}',r['text']):
                for key in m[1].split(','):
                    require(key in bibs(content(COMMIT,r['path'])),'new citation target '+key)
                    citations.append({'path':r['path'],'line':r['line'],'key':key})
        if r['path'].endswith('.md'):
            for target in re.findall(r'\]\(([^)]+)\)',r['text']):
                if '://' in target or target.startswith('#'):continue
                resolved=posixpath.normpath(posixpath.join(posixpath.dirname(r['path']),target))
                oid=git('rev-parse',COMMIT+':'+resolved).decode().strip()
                links.append({'path':r['path'],'line':r['line'],'literal_target':target,'resolved_path':resolved,'git_object':oid})
    previous=Path('/tmp/review_surreal_foundations_abba38172.md')
    require(sha(previous.read_bytes())=='3ba28c536a6f6d34886c9fc0850243c61eb62ace24e57a3a9d4c577817bfdcec','prior scoped review pin')
    require(sha(content(COMMIT,HSET))=='7efd58ce3aba38c3c8864a127ef7a6f032dc7ba6d3d2588346bc04b89ece67f9','cited hset bytes match earlier immutable review')
    totals={'changed_files':len(files),'text_files':sum('hunks' in f for f in files),'pdf_files':sum(f['path'].endswith('.pdf') for f in files),
            'text_additions':sum(f.get('added_lines',0) for f in files),'text_deletions':sum(f.get('removed_lines',0) for f in files),
            'full_text_diff_lines':sum(f.get('diff_lines',0) for f in files),'read_span_records':len(reads),
            'selected_interface_lines':sum(z-a+1 for rs in extra.values() for a,z in rs),
            'literal_added_label_occurrences':len(routes),'new_citation_occurrences':len(citations),'new_local_markdown_links':len(links)}
    require(totals['text_additions']==97 and totals['text_deletions']==5,'commit edit counts')
    result={'schema':'bounded reciprocal-publication review v1','commit':COMMIT,'parent':parent,
            'collector_sha256':sha(Path(__file__).read_bytes()),'files':files,'human_read_spans':reads,
            'label_index_files':index_files,'added_label_routes':routes,'new_citations':citations,'new_local_markdown_links':links,
            'prior_review_context':{'path':str(previous),'sha256':sha(previous.read_bytes()),'scope':'Prior bounded foundations review; neither its collector nor any predecessor was run/imported'},
            'findings':[],'assessment':'No new correction found in the four full text diffs and selected cited interfaces.',
            'totals':totals,'limits':['PDF bytes only; no build, render, page count or auxiliary-label numbering certification.',
            'No complete manuscript, archive placement, external-foundation or Lean proof audit.',
            'Literal target presence does not independently certify every target theorem.',
            'Earlier hset persistence-hypothesis and source-label-count corrections remain preserved in their review; this reciprocal commit changes neither.',
            'No finite ordinary-integer evaluator, paid compiler or arithmetic improvement follows from these semantic interpretation notes.'],
            'execution':'Fresh standard-library metadata collector only; Git object reads, no repository mutations, no supplied/frozen/archived/copied predecessor code execution or imports.'}
    encoded=(json.dumps(result,indent=2,ensure_ascii=False)+'\n').encode()
    if args.expect:require(args.expect.read_bytes()==encoded,'exact receipt replay')
    else:OUT.write_bytes(encoded)
    print(json.dumps({'status':'PASS','receipt_sha256':sha(encoded),**totals},sort_keys=True))

if __name__=='__main__':main()
