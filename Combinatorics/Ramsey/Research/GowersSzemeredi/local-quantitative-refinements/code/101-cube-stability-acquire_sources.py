#!/usr/bin/env python3
"""Acquire a limited source inventory without claiming a mathematical review."""
from __future__ import annotations
import concurrent.futures
import datetime
import json
import re
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parent
AUDIT=ROOT/'audit'
AUDIT.mkdir(exist_ok=True)
HEADERS={'User-Agent':'ProveIt-mathematical-source-audit/1.0','Accept':'application/vnd.github+json'}


def fetch(url: str, timeout: int=8) -> dict:
    item={'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        req=urllib.request.Request(url,headers=HEADERS)
        with urllib.request.urlopen(req,timeout=timeout) as response:
            raw=response.read(15_000_000)
            item['http_status']=response.status
            item['content_type']=response.headers.get('Content-Type','')
        text=raw.decode('utf-8',errors='replace')
        try:
            item['data']=json.loads(text)
        except json.JSONDecodeError:
            item['text']=text
        item['status']='retrieved'
    except Exception as exc:
        item['status']='failed'
        item['error']=f'{type(exc).__name__}: {exc}'
    return item


def safe(text: object) -> str:
    text=unicodedata.normalize('NFKD',str(text)).encode('ascii','ignore').decode()
    replacements={'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$',
                  '#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}'}
    return ''.join(replacements.get(c,c) for c in text)


def acquire_repo(repo: str) -> dict:
    base='https://api.github.com/repos/'+repo
    meta=fetch(base)
    branch=meta.get('data',{}).get('default_branch','main')
    endpoints={'recent_commits':base+'/commits?per_page=8',
               'tree':base+'/git/trees/'+urllib.parse.quote(branch,safe='')+'?recursive=1',
               'readme': 'https://raw.githubusercontent.com/'+repo+'/'+branch+'/README.md'}
    result={'repository':repo,'metadata':meta,'default_branch_used':branch}
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        futures={pool.submit(fetch,url):name for name,url in endpoints.items()}
        for future in concurrent.futures.as_completed(futures):
            result[futures[future]]=future.result()
    paths=[entry['path'] for entry in result.get('tree',{}).get('data',{}).get('tree',[])
           if entry.get('type')=='blob']
    if repo.endswith('/ProveIt'):
        selected=[p for p in paths if 'combinatorics/ramsey' in p.lower() and p.lower().endswith(('.tex','.md','.lean'))]
    else:
        selected=[p for p in paths if p.lower().endswith(('.tex','.md'))]
    result['selected_paths']=selected[:100]
    result['selection_note']='Deterministic filename inventory only; mathematical contents not independently reviewed.'
    slug=repo.replace('/','__')
    (AUDIT/(slug+'.json')).write_text(json.dumps(result,indent=2),encoding='utf-8')
    text=result.get('readme',{}).get('text')
    if text is not None:
        (AUDIT/(slug+'__README.txt')).write_text(text,encoding='utf-8')
    return result


def main() -> None:
    audit={'status_note':'Limited source inventory, not an exhaustive review or proof/novelty certification.',
           'requested_repositories':['openai/math','VladimirReshetnikov/ProveIt']}
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        audit['repositories']=list(pool.map(acquire_repo,audit['requested_repositories']))
    url='https://api.crossref.org/works?query.title='+urllib.parse.quote('Large values of the Gowers Host Kra seminorms')+'&rows=3'
    audit['contextual_bibliography_lookup']=fetch(url)
    (ROOT/'source_audit.json').write_text(json.dumps(audit,indent=2),encoding='utf-8')
    lines=[r'\subsection*{Machine-recorded inventory}',
           'The entries below are automatically extracted metadata. They are not endorsements of the claims in the corresponding files.']
    for repo in audit['repositories']:
        lines += [r'\subsubsection*{'+safe(repo['repository'])+'}']
        meta=repo['metadata']
        if meta['status']!='retrieved':
            lines += ['Repository metadata retrieval failed: '+safe(meta.get('error','unknown error'))+'.']
        else:
            lines += ['Default branch reported by the API: '+r'\texttt{'+safe(repo['default_branch_used'])+'}.']
        commits=repo.get('recent_commits',{}).get('data',[])
        if isinstance(commits,list) and commits:
            lines += [r'\begin{itemize}[leftmargin=*]']
            for c in commits[:4]:
                msg=c.get('commit',{}).get('message','').split('\n')[0][:130]
                date=c.get('commit',{}).get('committer',{}).get('date','')
                lines += [r'\item '+safe(date)+'; '+r'\texttt{'+safe(c.get('sha','')[:12])+'}: '+safe(msg)]
            lines += [r'\end{itemize}']
        else:
            lines += ['No readable recent-commit list was retrieved.']
        paths=repo.get('selected_paths',[])
        if paths:
            lines += ['Selected source paths (truncated inventory):',r'\begin{itemize}[leftmargin=*]']
            for path in paths[:8]:
                lines += [r'\item \path{'+path.replace('}','')+'}']
            lines += [r'\end{itemize}']
        else:
            lines += ['No selected source-path inventory was retrieved.']
        if repo.get('tree',{}).get('data',{}).get('truncated'):
            lines += [r'\textbf{The GitHub tree response was truncated.}']
    (ROOT/'repository_snapshot.tex').write_text('\n'.join(lines)+'\n',encoding='utf-8')
    print(json.dumps({'source_audit_written':True,
                      'repositories':[{'repository':r['repository'],'metadata_status':r['metadata']['status'],
                                       'selected_path_count':len(r.get('selected_paths',[]))} for r in audit['repositories']]},indent=2))

if __name__=='__main__':
    main()
