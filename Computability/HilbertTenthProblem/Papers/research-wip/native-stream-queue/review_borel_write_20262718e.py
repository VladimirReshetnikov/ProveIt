#!/usr/bin/env python3
"""Fresh inert metadata collector; never executes/imports delivered or predecessor code."""
import argparse, hashlib, io, json, re, subprocess, zipfile
from pathlib import Path
from collections import Counter
ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
COMMIT='20262718efdb5ef8545da72c2543c90c074bccf9'
PLACEMENT='54ece48ab0b52e823bd66814b38c330b9198224b'
HOST='Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/'
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
def sha(b): return hashlib.sha256(b).hexdigest()
def require(x,msg):
    if not x: raise ValueError(msg)
def git(*args): return subprocess.check_output(['git','-C',str(ROOT),*args])
def data(c,p): return git('show',c+':'+p)
def meta(b):
    d={'bytes':len(b),'sha256':sha(b)}
    try: b.decode('utf8'); d['lines']=len(b.splitlines())
    except UnicodeDecodeError: pass
    return d
def blob(c,p):
    b=data(c,p)
    return dict(commit=c,path=p,blob=git('rev-parse',c+':'+p).decode().strip(),**meta(b))
def span(b,a,z,mode='human read'):
    ls=b.splitlines(keepends=True)
    require(1<=a<=z<=len(ls),'span bounds')
    s=b''.join(ls[a-1:z]); s.decode('utf8')
    return {'first_line':a,'last_line':z,'mode':mode,**meta(s)}
def labels(b): return re.findall(rb'\\label(?:\[[^\]]*\])?\{([^{}]+)\}',b)
def refs(b):
    return sorted(set(x.strip().decode() for group in re.findall(rb'\\(?:[cC]ref|eqref|ref|pageref|autoref)\*?(?:\[[^\]]*\])?\{([^{}]+)\}',b) for x in group.split(b',') if x.strip()))
def context(p,ranges,c=COMMIT,mode='human read'):
    b=data(c,p)
    return dict(**blob(c,p),read_spans=[span(b,a,z,mode) for a,z in ranges])
def main():
    parent=git('rev-parse',COMMIT+'^').decode().strip()
    changed=git('diff','--name-status','--no-renames',parent,COMMIT)
    paths=[line.split('\t')[-1] for line in changed.decode().splitlines()]
    require(paths==[HOST+x for x in ['README.md','article.pdf','article.tex']],'changed paths')
    before=data(parent,HOST+'article.tex'); after=data(COMMIT,HOST+'article.tex')
    oldlabels=labels(before); newlabels=labels(after)
    require(len(newlabels)==len(set(newlabels)), 'duplicate host label')
    require(set(oldlabels)<=set(newlabels),'lost label')
    obj={'schema':'borel-publication-immutable-review-v1','commit':COMMIT,'parent':parent,
         'helper_sha256':sha(Path(__file__).read_bytes()),'changed_path_output':meta(changed),
         'commit_message':meta(git('show','-s','--format=%B',COMMIT)),
         'changed_files':[{'before':blob(parent,p),'after':blob(COMMIT,p),'coverage':'PDF hash only' if p.endswith('.pdf') else 'text scope below'} for p in paths]}
    diffs=[]
    for f,ranges in [('README.md',[(1,733)]),('article.tex',[(1,790)])]:
        b=git('diff','--no-ext-diff','--no-renames','--unified=3',parent,COMMIT,'--',HOST+f)
        diffs.append({'path':HOST+f,'arguments':['--no-ext-diff','--no-renames','--unified=3'],**meta(b),
                      'read_spans':[span(b,a,z,'full changed guide diff' if f=='README.md' else 'selected raw diff, front matter and earlier-part editorial additions') for a,z in ranges]})
    obj['diffs']=diffs
    article_ranges=[(6237,6247),(35395,35425),(36695,36757),(39200,39395),(40067,40143),(40450,40793),(40800,40902),(41125,41237),(44582,44636),(45010,45292),(46441,46621),(47255,47380),(47478,47516)]
    obj['local_reads']=[context(HOST+'article.tex',article_ranges),
        context('Algebra/SurrealNumbers/AGENTS.md',[(1,182)]),context('docs/incoming/README.md',[(426,439)])]
    lean={
      'Algebra/BakerCampbellHausdorff/Lean/BCH/Eigen.lean':[(1,105),(208,244)],
      'Algebra/BakerCampbellHausdorff/Lean/BCH/Main.lean':[(1,85)],
      'Algebra/SurrealNumbers/Surreal/HahnSeries/EulerDerivation.lean':[(135,194)],
      'Algebra/SurrealNumbers/Surreal/HahnSeries/StrongEvaluation.lean':[(20,65)],
      'Algebra/SurrealNumbers/Surreal/Algebra/LaurentResidueChange.lean':[(1,30),(218,252)]}
    for p,r in lean.items():
        require((ROOT/p).read_bytes()==data(COMMIT,p),'working Lean bytes differ from immutable reviewed source')
        obj['local_reads'].append(context(p,r,mode='static Lean declaration/interface read; no build/axiom audit'))
    placement_path=WIP+'review_borel_placement_54ece48ab.json'
    placement_bytes=data(COMMIT,placement_path); placement=json.loads(placement_bytes)
    obj['placement_locator']=dict(**blob(COMMIT,placement_path),coverage='inert parsed locator; independent checks below')
    obj['prior_reviews']=[]
    for r in placement['prior_reviews']:
        item={}
        for ext in ['md','json','py']:
            p=r[ext]['path']; b=data(COMMIT,p)
            require(sha(b)==r[ext]['sha256'],'prior review changed')
            item[ext]=dict(**blob(COMMIT,p),coverage='full prior note read' if ext=='md' else 'hash only; no replay')
            if ext=='md':item[ext]['read_spans']=[span(b,1,len(b.splitlines()),'full prior review note; original manuscript coverage inherited, not newly re-read')]
        obj['prior_reviews'].append(item)
    p=WIP+'review_borel_placement_54ece48ab.md';b=data(COMMIT,p)
    obj['local_reads'].append(context(p,[(1,len(b.splitlines()))]))
    archives=[]; archive_members={};routes=[]
    for source,a in zip([24,25,26,27],placement['archives']):
        arr=a['arrival']; b=data(arr['commit'],arr['path'])
        require(sha(b)==arr['sha256'],'archive arrival pin')
        require(b==data(a['commit'],a['path']),'arrival and pre-placement archive differ')
        z=zipfile.ZipFile(io.BytesIO(b)); members={i.filename:z.read(i) for i in z.infolist() if not i.is_dir()}
        archive_members[a['path']]=members
        ms=[]
        for inf in z.infolist():
            if inf.is_dir():continue
            mb=members[inf.filename]
            ms.append(dict(path=inf.filename,compressed_bytes=inf.compress_size,crc32=f'{inf.CRC:08x}',**meta(mb),coverage='hash/inventory only in this publication review'))
        # Parse actual delivered checksum bytes, independently of prior receipt entries.
        manifest=a['manifest']; checks=[]
        for line in members[manifest].decode().splitlines():
            if not line.strip():continue
            digest, name=line.split(None,1);name=name.lstrip('*')
            candidates=[name,str(Path(manifest).parent/name)]
            names=[p for p in candidates if p in members]
            require(bool(names),'manifest path')
            name=names[0];require(sha(members[name])==digest,'manifest digest')
            checks.append({'path':name,'sha256':digest})
        require(set(x['path'] for x in checks)==set(members)-{manifest},'manifest coverage')
        texnames=[n for n in members if n.endswith('.tex')];require(len(texnames)==1,'tex count')
        tex=members[texnames[0]];labs=labels(tex);prefix=a['planned_label_prefix']
        lr=[]
        for label in labs:
            target=prefix+label.decode()
            lr.append({'source_label':label.decode(),'host_label':target,'exists':target.encode() in set(newlabels)})
        routes.append({'source':source,'archive':a['path'],'member':texnames[0],'sha256':sha(tex),'prefix':prefix,'labels':lr,
                       'coverage':'literal label locators only; no full body-equivalence certification'})
        archives.append(dict(source=source,**blob(arr['commit'],arr['path']),members=ms,manifest=manifest,checksums=checks,
                              absent_at_publication=git('ls-tree',COMMIT,'--',arr['path'])==b''))
    obj['archives']=archives;obj['source_label_routes']=routes
    placements=[]
    for p in placement['placements']:
        b=data(COMMIT,p['path']); member=archive_members[p['archive_path']][p['member']]
        require(b==member==data(PLACEMENT,p['path']),'placed member bytes')
        placements.append(dict(path=p['path'],archive_path=p['archive_path'],member=p['member'],**meta(b),
                         at_publication=blob(COMMIT,p['path']),first_placement=blob(PLACEMENT,p['path']),byte_identical=True))
    obj['placements']=placements
    obj['host_preimage_equals_placement']={f:data(parent,HOST+f)==data(PLACEMENT,HOST+f) for f in ['README.md','article.tex','article.pdf']}
    require(all(obj['host_preimage_equals_placement'].values()),'host preimage placement')
    nr=refs(after); labset={x.decode() for x in newlabels}
    cites=sorted(set(x.strip().decode() for grp in re.findall(rb'\\cite\w*\*?(?:\[[^\]]*\])*\{([^{}]+)\}',after) for x in grp.split(b',') if x.strip()))
    bibkeys=sorted(set(x.decode() for x in re.findall(rb'\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}',after)))
    obj['label_inventory']={'scope':'literal regular expressions including optional label argument; no macro expansion/TeX build',
       'before':[x.decode() for x in oldlabels],'after':[x.decode() for x in newlabels],
       'added':sorted(labset-{x.decode() for x in oldlabels}),'lost':[],'part_heading_count_before':len(re.findall(rb'\\part\{',before)),'part_heading_count_after':len(re.findall(rb'\\part\{',after)),
       'literal_ref_targets':nr,'unresolved_literal_refs':sorted(set(nr)-labset),
       'literal_cite_targets':cites,'literal_bibitems':bibkeys,'unresolved_literal_cites':sorted(set(cites)-set(bibkeys))}
    obj['peer_reviews']=[]
    for stem,pins in [('review_pma_borel_flow_interfaces_20262718e',{'md':'0435b3a73e1cd47de1b149420377f8b1bf9414a9b5de96c30590fa824945c4fa','json':'69a1e79c1f0e6c1ad1893304b805c5bfb2b62da2ec266ec9914c811a98dd36ec'})]:
        peer={}
        for ext,h in pins.items():
            p=Path('/tmp')/(stem+'.'+ext);b=p.read_bytes();require(sha(b)==h,'peer pin');peer[ext]={'path':str(p),**meta(b)}
        j=json.loads((Path('/tmp')/(stem+'.json')).read_bytes())
        for f in j['files']:
            b=data(COMMIT,f['path']);require(sha(b)==f['sha256'],'peer blob')
            for s in f['read_spans']:
                ss=span(b,s['start_line'],s['end_line'])
                require(ss['sha256']==s['sha256'] and ss['bytes']==s['bytes'],'peer span')
        peer['read_scope']=j;peer['provenance']='independent Tesla proof challenge; not claimed as Pascal reading'
        obj['peer_reviews'].append(peer)
    obj['findings']=[{'id':'R1','status':'false editorial scope, retained at immutable snapshot','paths':[HOST+'README.md',HOST+'article.tex'],
      'lines':{'README.md':[1040,1044],'article.tex':[36739,36744]},
      'claim':'V_Gamma is Sigma02-complete for nonzero cyclic Gamma and Pi11-complete otherwise',
      'counterexample':'Gamma={0}: every support is well ordered, so V_Gamma is the whole space. Article41144-41178 correctly separates this case; PartXVII35407-35409 expressly permits it.',
      'additional_guide_scope':'Replace undefined L in standard-Borel criterion by Gamma.'},
      {'id':'R2','status':'cited hypothesis mismatch; conclusion remains valid','path':HOST+'article.tex','lines':[6240,6246],
       'claim':'cor:roots excludes every dense exponent group',
       'counterexample_to_premise':'Gamma=Z+sqrt(2)Z is dense but no nonzero element has all dyadic divisions in Gamma. Use thm:groups; cor:roots40135-40143 has the stronger premise.'},
      {'id':'R3','status':'overbroad provenance wording','paths':[HOST+'README.md',HOST+'article.tex'],
       'claim':'All four archives were read in full.',
       'qualification':'Earlier reviews read all manuscripts, but PDFs were hash-only and some saved evidence had selected reads. No whole-archive human read is inherited.'},
      {'id':'Q1','status':'qualification of earlier review, not new publication defect',
       'claim':'Old flow intake blanket no substantive error does not extend to its unqualified sampling remark.',
       'resolution':'Publication retains finite-rank counterexample and proves infinite-rank sampling extension. Independent Tesla challenge passes within recorded spans.'}]
    obj['limits']=['Only fresh reviewer metadata code executed; no delivered/archived/committed/frozen/copied predecessor code or builders.',
       'No PDF reading/build/page-count certification, external paper/priority audit or Lean build/axiom audit.',
       'Full changed guide diff read; only stated article/diff and Lean spans read. No full 10000-line proof audit or normalized source-body equivalence.',
       'Source suite pass counts, author reruns, 8-gram overlap and external inspection statements remain attributed claims.',
       'Borel/real/infinite certificate results do not supply an ordinary-integer paid fixed-arity universal compiler.']
    obj['totals']={'changed_files':len(paths),'before_after_blobs':2*len(paths),'raw_diffs':len(diffs),'archives':len(archives),
      'regular_members':sum(len(a['members']) for a in archives),'delivered_checksums':sum(len(a['checksums']) for a in archives),
      'placements':len(placements),'source_labels':sum(len(r['labels']) for r in routes),
      'direct_prefix_routes_present':sum(x['exists'] for r in routes for x in r['labels']),
      'host_labels_before':len(oldlabels),'host_labels_after':len(newlabels),'host_labels_added':len(obj['label_inventory']['added']),
      'local_article_postimage_lines':sum(z-a+1 for a,z in article_ranges),'guide_rawdiff_lines_read':733,'article_rawdiff_lines_read':790}
    obj['result']='PASS for stated metadata checks; R1 requires editorial correction; bounded proof scope only'
    ap=argparse.ArgumentParser();g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output');g.add_argument('--expect');args=ap.parse_args()
    out=(json.dumps(obj,indent=2,sort_keys=True,ensure_ascii=False)+'\n').encode()
    if args.output:
        with open(args.output,'xb') as f:f.write(out)
    else: require(Path(args.expect).read_bytes()==out,'exact receipt replay')
    print(json.dumps(obj['totals'],sort_keys=True));print('PASS')
if __name__=='__main__':main()
