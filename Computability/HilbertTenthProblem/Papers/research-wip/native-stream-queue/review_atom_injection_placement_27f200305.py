#!/usr/bin/env python3
"""Fresh read-only Git/ZIP placement audit; never executes delivered code."""
import argparse
import hashlib
import io
import json
import re
import stat
import subprocess
import zipfile
from pathlib import Path

COMMIT='27f2003053ae8f4f6bbccdc70b9e2dcb70b40238'
PARENT='b399cbd29592092e38af0a7c8d5427bfd3f8fff7'
ARRIVAL='26e036956381b07bb43de0187965f8dcdf9194fb'
SOURCE_PIN='715a716a3002b1e9f28daa2d81c009a392851b94'
HOST='SetTheory/Cardinals/docs/reports/ordinals-and-order-types/naming-elementary-embeddings/'
REVIEW='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_new_actions_26e036956'
REVIEW_PINS={'.md':'55d864059205571c3eeab0d7522c72eaf7ea064c692fa9672dd10a7adc8b0a37','.json':'9958f93dc6e3a807adc09829cee77b804d08818441ddd0f0abe50ea0a707f91c'}
ARCHIVES={
 'docs/incoming/atom_actions_research.zip':'c7f96e8905fb0da490c3960b0afdb6bde92fcb96673782ebfc1a2c1a160ce264',
 'docs/incoming/commuting_injections_research.zip':'15d35b3a01bddc25a3fc47f4f39b262789d5f91928a91a566987f198371b0433'}
MAP={
 'code/03-atom-actions-make_figure.py':('atom_actions_research.zip','atom_actions/figures/make_figure.py'),
 'code/03-atom-actions-verify_presentations.py':('atom_actions_research.zip','atom_actions/verify_presentations.py'),
 'code/04-commuting-injections-verify_results.py':('commuting_injections_research.zip','commuting_injections/verify_results.py'),
 'data/03-atom-actions-verification_results.json':('atom_actions_research.zip','atom_actions/verification_results.json'),
 'data/04-commuting-injections-verification.json':('commuting_injections_research.zip','commuting_injections/verification.json'),
 'figures/03-atom-actions-antichain_upsets.pdf':('atom_actions_research.zip','atom_actions/figures/antichain_upsets.pdf'),
 'figures/03-atom-actions-antichain_upsets.png':('atom_actions_research.zip','atom_actions/figures/antichain_upsets.png')}

def require(ok,what):
    if not ok: raise ValueError(what)

def sha(raw): return hashlib.sha256(raw).hexdigest()

def git(repo,*args):
    return subprocess.check_output(['git','-C',str(repo),*args])

def meta(raw): return {'bytes':len(raw),'sha256':sha(raw)}

def blob(repo,commit,path):
    raw=git(repo,'show',commit+':'+path)
    return raw,dict(meta(raw),commit=commit,path=path,blob=git(repo,'rev-parse',commit+':'+path).decode().strip())

def span(raw,first,last):
    lines=raw.decode('utf-8').splitlines()
    require(1<=first<=last<=len(lines),'read span')
    return {'first_line':first,'last_line':last,'normalized_utf8_sha256':sha(('\n'.join(lines[first-1:last])+'\n').encode())}

def build(repo):
    require(git(repo,'rev-parse',COMMIT+'^').decode().strip()==PARENT,'parent')
    raw=git(repo,'diff-tree','--no-commit-id','--name-status','-r',COMMIT)
    changes=[dict(zip(('status','path'),line.split('\t'))) for line in raw.decode().splitlines()]
    expected={('A',HOST+p) for p in MAP}|{('D',p) for p in ARCHIVES}
    require({(x['status'],x['path']) for x in changes}==expected and len(changes)==9,'exact change set')
    diff=git(repo,'diff','--binary','--no-ext-diff','--no-textconv',PARENT,COMMIT,'--')
    message=git(repo,'show','--format=%B','--no-patch',COMMIT)
    inherited=[]
    for ext,pin in REVIEW_PINS.items():
        b,m=blob(repo,COMMIT,REVIEW+ext); require(sha(b)==pin,'inherited review pin')
        if ext=='.md':m['read_spans']=[span(b,1,len(b.decode().splitlines()))]
        else:m['scope']='parsed inert archive inventory and declared review scopes, not replayed'
        inherited.append(m)
    earlier=json.loads(git(repo,'show',COMMIT+':'+REVIEW+'.json'))
    older={a['path']:a for a in earlier['archives']}
    archives=[];members={};manifest_count=0
    for path,pin in ARCHIVES.items():
        raw,m=blob(repo,PARENT,path); require(sha(raw)==pin,'archive hash')
        arrived,am=blob(repo,ARRIVAL,path);require(arrived==raw,'arrival retention')
        require(older[path]['sha256']==pin,'earlier archive pin')
        m['arrival']=am;m['absent_at_placement']=True;m['members']=[]
        tree=git(repo,'ls-tree','--name-only',COMMIT,'--',path);require(not tree.strip(),'retirement')
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            for inf in z.infolist():
                require(not inf.is_dir() and stat.S_IFMT(inf.external_attr >> 16) in (0, stat.S_IFREG),'all entries regular')
                b=z.read(inf);members[(Path(path).name,inf.filename)]=b
                d=dict(meta(b),path=inf.filename,crc32=f'{inf.CRC:08x}',compressed_bytes=inf.compress_size,external_attr=inf.external_attr)
                prior=next(x for x in older[path]['members'] if x['path']==inf.filename)
                require(prior['sha256']==sha(b) and prior['bytes']==len(b),'prior member inventory')
                destinations=[HOST+p for p,pair in MAP.items() if pair==(Path(path).name,inf.filename)]
                d['placed_paths']=destinations;d['coverage']='byte authentication only'
                if inf.filename.endswith(('README.txt','SHA256SUMS.txt')):
                    d['read_spans']=[span(b,1,len(b.decode().splitlines()))];d['coverage']='full text read'
                if inf.filename.endswith('SHA256SUMS.txt'):
                    checks=[]
                    for line in b.decode().splitlines():
                        digest,short=line.split(None,1);member=str(Path(inf.filename).parent/short.strip())
                        require(sha(z.read(member))==digest,'internal manifest')
                        checks.append({'member':member,'sha256':digest})
                    d['manifest_verified']=checks;manifest_count+=len(checks)
                m['members'].append(d)
        archives.append(m)
    placements=[]
    for path,pair in MAP.items():
        b,m=blob(repo,COMMIT,HOST+path);require(b==members[pair],'literal placement '+path)
        m.update({'archive':'docs/incoming/'+pair[0],'member':pair[1],'byte_identical':True})
        placements.append(m)
    host=[];reads=[]
    spans={'README.md':[(1,26),(407,477),(579,601)],'article.tex':[(163,174),(1102,1118)]}
    for path in ['README.md','article.tex','article.pdf','SOURCE_AUDIT.md']:
        current,m=blob(repo,COMMIT,HOST+path);before,bm=blob(repo,PARENT,HOST+path)
        pinned,pm=blob(repo,SOURCE_PIN,HOST+path)
        require(current==before==pinned,'unchanged host '+path)
        m.update({'parent_blob':bm['blob'],'source_pin_blob':pm['blob'],'unchanged_from_parent_and_source_pin':True})
        if path in spans:m['read_spans']=[span(current,*s) for s in spans[path]]
        if path=='article.tex':
            text=current.decode();labels=re.findall(r'\\label\s*\{([^{}]+)\}',text)
            parts=[{'line':i+1,'text':line} for i,line in enumerate(text.splitlines()) if re.match(r'\s*\\part\{',line)]
            require(len(parts)==2 and not any(x.startswith(('nee:aa:','nee:ci:')) for x in labels),'no new PartIII labels')
            m['literal_label_count']=len(labels);m['literal_parts']=parts
            m['new_label_prefixes_present']=False
        host.append(m)
    b,m=blob(repo,COMMIT,'docs/incoming/README.md');m['read_spans']=[span(b,411,440)];reads.append(m)
    require(len(archives)==2 and sum(len(x['members']) for x in archives)==14,'member count')
    require(len(placements)==7 and sum(x['bytes'] for x in placements)==228956,'placed byte count')
    require(manifest_count==8,'eight manifest entries')
    return {'schema':'atom-injection-placement-review-v1','reviewer_sha256':sha(Path(__file__).read_bytes()),
     'commit':COMMIT,'parent':PARENT,'arrival':ARRIVAL,'source_pin':SOURCE_PIN,
     'commit_message':dict(meta(message),read_spans=[span(message,1,len(message.decode().splitlines()))]),
     'changed_paths':changes,'raw_binary_diff':dict(meta(diff),read_scope='change names/status only; full diff hashed, not a new full script/data read'),
     'archives':archives,'placements':placements,'unchanged_host_files':host,'context_reads':reads,'inherited_review':inherited,
     'totals':{'archives':2,'regular_members':14,'placed_files':7,'placed_bytes':228956,'deleted_archives':2,'manifest_entries_verified':8},
     'scope':{'ancillary_placement_only':True,'new_manuscript_publication_evidenced':False,'article_or_guide_modified':False,
      'supplied_program_execution':False,'predecessor_replay':False,'build_or_pdf_render':False,'new_mathematical_review':False,'repository_mutation':False}}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args()
    raw=(json.dumps(build(a.repo),sort_keys=True,indent=2)+'\n').encode()
    if a.output:
        with a.output.open('xb') as stream:stream.write(raw)
    else:require(a.expect.read_bytes()==raw,'receipt mismatch')
    print('PASS:7 byte-identical placements,14 members,8 checksums;4 host files unchanged; no PartIII publication delta.')
if __name__=='__main__':main()
