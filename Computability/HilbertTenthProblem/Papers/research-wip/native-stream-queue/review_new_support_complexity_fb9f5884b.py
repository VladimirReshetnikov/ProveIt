#!/usr/bin/env python3
"""Fresh read-only archive/provenance metadata. No delivered code is executed."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import zipfile

REPO=Path('/home/codex/.codex/worktrees/2a71/Proofs')
SNAPSHOT='fb9f5884b'
ARRIVAL='7be14aa84'
ARCHIVE='docs/incoming/glazer_proveit_support_complexity.zip'
PREFIX='glazer_proveit_support_complexity/'
LEAN_COMMIT='c39974f12a45c8795575ab222f3b84b2901c394f'
LEAN_PATH='Algebra/SurrealNumbers/Surreal/HahnSeries/StrongEvaluation.lean'

def guard(test,msg):
 if not test:raise RuntimeError(msg)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=REPO)
def pin(commit,path):
 raw=git('show',commit+':'+path)
 return raw,{'commit':git('rev-parse',commit).decode().strip(),'path':path,'blob':git('rev-parse',commit+':'+path).decode().strip(),'bytes':len(raw),'sha256':sha(raw)}
def span(raw,start,end,label):
 lines=raw.splitlines(keepends=True);part=b''.join(lines[start-1:end])
 guard(1<=start<=end<=len(lines),'span bounds')
 return {'start':start,'end':end,'label':label,'bytes':len(part),'sha256':sha(part)}
def line_at(text,offset):return text.count('\n',0,offset)+1

def make():
 raw,archive=pin(SNAPSHOT,ARCHIVE);arrival_raw,arrival=pin(ARRIVAL,ARCHIVE)
 guard(raw==arrival_raw,'arrival/snapshot byte equality')
 parent=git('rev-parse',ARRIVAL+'^').decode().strip()
 parent_files=git('ls-tree','-r','--name-only',parent,'--',ARCHIVE).decode().splitlines()
 guard(parent_files==[],'archive absent immediately before arrival')
 z=zipfile.ZipFile(io.BytesIO(raw));members=[];payload={}
 for info in z.infolist():
  guard(not info.is_dir() and info.filename.startswith(PREFIX),'expected file member')
  content=z.read(info);payload[info.filename]=content;name=info.filename[len(PREFIX):]
  guard(name not in ('','..') and '/' not in name,'flat safe member name')
  full_text=name!='article.pdf'
  records=[]
  if full_text:
   n=len(content.splitlines());records=[span(content,1,n,'full inert text read')]
  members.append({'path':info.filename,'bytes':len(content),'compressed_bytes':info.compress_size,'crc32':format(info.CRC,'08x'),'sha256':sha(content),'coverage':'full inert text read' if full_text else 'hash only; no visual or proof inspection','read_spans':records})
 guard(len(members)==8,'eight members')
 manifest=[]
 for line in payload[PREFIX+'SHA256SUMS'].decode().splitlines():
  digest,name=line.split(None,1);name=name.strip();content=payload[PREFIX+name]
  guard(sha(content)==digest,'delivered manifest '+name)
  manifest.append({'name':name,'sha256':digest})
 guard(len(manifest)==7 and {r['name'] for r in manifest}=={m['path'][len(PREFIX):] for m in members}-{'SHA256SUMS'},'manifest exact seven-file coverage')
 tex=payload[PREFIX+'article.tex'].decode();labels=[];references=[];citations=[]
 for m in re.finditer(r'\\label(?:\[[^\]]*\])?\{([^{}]+)\}',tex):labels.append({'key':m.group(1),'line':line_at(tex,m.start())})
 names=[r['key'] for r in labels];guard(len(names)==len(set(names)),'unique article labels')
 for m in re.finditer(r'\\(eqref|ref|autoref|[cC]ref)\*?(?:\[[^\]]*\])?\{([^{}]+)\}',tex):
  for key in m.group(2).split(','):references.append({'command':m.group(1),'key':key.strip(),'line':line_at(tex,m.start())})
 bib=[m.group(1) for m in re.finditer(r'\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}',tex)]
 for m in re.finditer(r'\\(?:cite|citep|citet|Cite)\*?(?:\[[^\]]*\])*\{([^{}]+)\}',tex):
  for key in m.group(1).split(','):citations.append({'key':key.strip(),'line':line_at(tex,m.start())})
 guard(all(r['key'] in names for r in references),'all local references resolved')
 guard(all(r['key'] in bib for r in citations),'all bibliography references resolved')
 lraw,lean=pin(LEAN_COMMIT,LEAN_PATH);lean['read_spans']=[span(lraw,1,len(lraw.splitlines()),'full pinned Lean source read; no build or imports traversed')]
 symbols=['def PowerSeriesSummable','theorem evaluate_powerSeriesSum','theorem summable_evaluate_powerSeries','isPWO_iUnion_support\'','finite_co_support\'']
 lean['observed_symbols']={s:[i for i,line in enumerate(lraw.decode().splitlines(),1) if s in line] for s in symbols}
 guard(all(lean['observed_symbols'].values()),'stated Lean symbols')
 instructions=[]
 for name,ranges in [('Algebra/SurrealNumbers/AGENTS.md',None),('docs/incoming/README.md',[(426,438)])]:
  iraw,record=pin(SNAPSHOT,name)
  record['read_spans']=[span(iraw,1,len(iraw.splitlines()),'full applicable instructions read')] if ranges is None else [span(iraw,a,b,'claim-retention standing rule') for a,b in ranges]
  instructions.append(record)
 return {'schema':'support complexity immutable intake review v1','collector_sha256':sha(Path(__file__).read_bytes()),'snapshot':git('rev-parse',SNAPSHOT).decode().strip(),'arrival':arrival,'archive':archive,'arrival_parent':parent,'archive_absent_in_arrival_parent':True,'unchanged_archive_at_snapshot':True,'archive_members':members,'delivered_manifest':manifest,'article_structure':{'line_count':len(tex.splitlines()),'labels':labels,'references':references,'bibliography_keys':bib,'citations':citations,'unresolved_references':[],'unresolved_citations':[]},'pinned_lean_read':lean,'instructions':instructions,'scope':{'article_full_read':True,'external_papers_read_or_certified':False,'prior_Library_question_verified':False,'pdf_rendered_or_compared':False,'delivered_checker_executed':False,'build_executed':False,'new_Lean_theorem_certified':False,'repository_mutation':False},'status':'PASS'}

def main():
 p=argparse.ArgumentParser();g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();result=make();raw=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
 if a.output:
  with a.output.open('xb') as f:f.write(raw)
 else:guard(raw==a.expect.read_bytes(),'exact receipt equality')
 s=result['article_structure'];print(json.dumps({'status':'PASS','members':len(result['archive_members']),'manifest':len(result['delivered_manifest']),'labels':len(s['labels']),'references':len(s['references']),'citations':len(s['citations']),'receipt_sha256':sha(raw)}))
if __name__=='__main__':main()
