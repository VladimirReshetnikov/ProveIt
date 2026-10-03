#!/usr/bin/env python3
"""Pinned byte-preservation/staging audit; no execution of archived programs.

python review_surreal_placement_ccc046989.py --repo /path/to/Proofs \
  --expect review_surreal_placement_ccc046989.json
All Git reads name immutable commits, never the caller's working tree/HEAD.
"""
from __future__ import annotations
import argparse, hashlib, io, json, re, stat, subprocess, zipfile
from pathlib import Path, PurePosixPath
if not __debug__:
    raise RuntimeError("Run this bounded audit with normal Python, not -O")
ARRIVAL = '4e270aa4648c5fd7e18626507531046715976535'
PLACEMENT = 'ccc046989e0d9c5556a8d2d8c1b81c3aa85e185d'
TARGET = 'Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders'
ARCHIVES = [{'archive': 'Surreal_Well_Orders_Research.zip',
  'label': 'research',
  'members': [{'path': 'surreal_well_orders/README.md',
               'sha256': '7d2a38c8a48685083851ae2e07a39d50a2f0011f5f10a7a13be8cd9983c29ba3',
               'size': 3750},
              {'path': 'surreal_well_orders/RESEARCH_STATUS.md',
               'sha256': 'b583206a78a401a6d40eec3fe2d14a1a4a1232c258cfd9322b6157154180696e',
               'size': 5239},
              {'path': 'surreal_well_orders/SHA256SUMS.txt',
               'sha256': '66a3c25862ed389c8c46b254da14aa81220213c570844d829036108a463e5b8a',
               'size': 570},
              {'path': 'surreal_well_orders/article.pdf',
               'sha256': 'e368b543d32d374c4e672c945bb3d3f0b0c739f3e8961477f62a5f31c0217105',
               'size': 334883},
              {'path': 'surreal_well_orders/article.tex',
               'sha256': 'bd87c866b520a5261178b28e23fb6df3bcbf2c431bd8414b46f919b022ffc56c',
               'size': 80261},
              {'path': 'surreal_well_orders/build.sh',
               'sha256': '3894153b599649376c75971722a7a377ab84b1b34280e80a955dad8b91453a66',
               'size': 221},
              {'path': 'surreal_well_orders/code/finite_checks.py',
               'sha256': '508bf3668241708b72043bff16bb64b559842b745572a2a6f05e4be65a8d2f64',
               'size': 10211},
              {'path': 'surreal_well_orders/data/finite_checks.json',
               'sha256': '29c3beb5bed2dce88b2a70fa0a55408ce5510b95016b7a93ce705edf28ea9460',
               'size': 576}],
  'sha256': '8aebf0ab80207a4e2165be6f7a329eff18b90134128b02e65c4732c97c252ee9'},
 {'archive': 'Surreal_Well_Orders_Research (1).zip',
  'label': 'research1',
  'members': [{'path': 'surreal_well_orders/surreal_well_orders.pdf',
               'sha256': 'd99f4a6c05f37c3a4c61118ceb05d2246f5d6dd2fbccf1fc07a575f665cfc256',
               'size': 352071},
              {'path': 'surreal_well_orders/surreal_well_orders.tex',
               'sha256': '2a3f5c055d64adc4f3954b1c0224e52c710f57873617d3f756c207ed26a4d4a0',
               'size': 95748},
              {'path': 'surreal_well_orders/README.md',
               'sha256': '5f63b9ee2fead063c4a9c23523996d699284acb1e12df8783790483033194eee',
               'size': 3966},
              {'path': 'surreal_well_orders/build.sh',
               'sha256': '081a9006286946109415a3b6b04bef6a3087df4c2c8ae015c0f4364725c22ce6',
               'size': 428},
              {'path': 'surreal_well_orders/verify_finite.py',
               'sha256': '2e429bc5a52702a922f44ee60b7e1a91dc9ef9924bc7c8649bfbae2069e843d5',
               'size': 3721},
              {'path': 'surreal_well_orders/verification_results.json',
               'sha256': '6d9bc26ba180fed1832106e605ab3c537b65be7ac481916d301050ddf076cf60',
               'size': 332},
              {'path': 'surreal_well_orders/SHA256SUMS.txt',
               'sha256': '8fa626f69eb33d7cf8e396cbc2a2a2e02db11170cc7f69d75cfac9172cea600a',
               'size': 506}],
  'sha256': '36c7f6ac22cd2a665aa078eb99eeffef170cb2d6c0cadab31417562f147d8179'},
 {'archive': 'surreal_well_orders.zip',
  'label': 'lower',
  'members': [{'path': 'surreal_well_orders/article.tex',
               'sha256': '44ce2e2de4bdf15373709b6c120be7e03eadd3d868149152fefb409ae0dcd450',
               'size': 79635},
              {'path': 'surreal_well_orders/article.pdf',
               'sha256': 'fee434ab4074dc736846e7322abba97e0c12ad2f3b4f72df39f2a98b606004a4',
               'size': 484264},
              {'path': 'surreal_well_orders/README.md',
               'sha256': '48ec3a58af77dcb314dcb2be5a517a1e405a12ef7e0bc0122d25190b3b93e78a',
               'size': 4326},
              {'path': 'surreal_well_orders/RESEARCH_STATUS.md',
               'sha256': '9536ab4b79e344bd2f6e5c80ffc9e16e0ac1e5bc6f7b289372d04b7d97b74904',
               'size': 8647},
              {'path': 'surreal_well_orders/build.sh',
               'sha256': '23e41596cf1fbe0d3d18c48b831c18915bf63b834183d570ae7aef456ba36c68',
               'size': 402},
              {'path': 'surreal_well_orders/code/finite_checks.py',
               'sha256': '2bacfce134b39479d910159486079aa5792550a1fe7e57c54b79d9605827f7a3',
               'size': 7326},
              {'path': 'surreal_well_orders/data/finite_checks.json',
               'sha256': 'b541630a53904c56aa8fbf2f2e6bb9a1b731735e58473608b44f4e90546e521c',
               'size': 845},
              {'path': 'surreal_well_orders/SHA256SUMS.txt',
               'sha256': 'a1118dc2384a9ccf0acf27d43972a9f257b158e24e1ea3aeb105a3f13963a4ba',
               'size': 570}],
  'sha256': '1edf59eaa0febdc0b7c9da581d9a6a65cc2ae88b99c166756ffd58f8aa4d4d5d'},
 {'archive': 'surreal_well_orders (1).zip',
  'label': 'lower1',
  'members': [{'path': 'surreal_well_orders/surreal_well_orders.tex',
               'sha256': 'b08eaac10e7cd7573713490422d6d3a590cdac8df890743b98c07c3f5742dac2',
               'size': 126780},
              {'path': 'surreal_well_orders/surreal_well_orders.pdf',
               'sha256': '7dbce2ecb7cd661514465887ff5ab68603ff0c7a46dc9c7f407744a67c513552',
               'size': 543575},
              {'path': 'surreal_well_orders/README.txt',
               'sha256': 'f0b5a8dd762e56fbf58b4bdeeea3eb5be1904926a396c1d2206a9d0ea21e8fd7',
               'size': 2414},
              {'path': 'surreal_well_orders/repository_audit.md',
               'sha256': '9332fff9474586f329927f9fc44c53ba53caf689ed3aee561fa44b4935130f39',
               'size': 10682},
              {'path': 'surreal_well_orders/finite_checks.py',
               'sha256': '751e173bf3529e93d86a0281e1385515ec8220a1b97ca682a2ecef8bd895b844',
               'size': 6538},
              {'path': 'surreal_well_orders/finite_checks_results.txt',
               'sha256': '997710f1aef157365105381378e0d4638f67092c847d3df8a93befbf561f52af',
               'size': 939}],
  'sha256': 'e48ab1b54681787324fd01953ba093d2b7abe546673ccd0f0a0bcb59e232e33a'}]
MAPPING = {'09-core-RESEARCH_STATUS.md': ('research', 'RESEARCH_STATUS.md'),
 '11-raw-orders-repository_audit.md': ('lower1', 'repository_audit.md'),
 '12-singular-RESEARCH_STATUS.md': ('lower', 'RESEARCH_STATUS.md'),
 'README.md': ('lower1', 'README.txt'),
 'article.tex': ('lower1', 'surreal_well_orders.tex'),
 'code/08-skeleton-build.sh': ('research1', 'build.sh'),
 'code/08-skeleton-verify_finite.py': ('research1', 'verify_finite.py'),
 'code/09-core-build.sh': ('research', 'build.sh'),
 'code/09-core-finite_checks.py': ('research', 'code/finite_checks.py'),
 'code/11-raw-orders-finite_checks.py': ('lower1', 'finite_checks.py'),
 'code/12-singular-build.sh': ('lower', 'build.sh'),
 'code/12-singular-finite_checks.py': ('lower', 'code/finite_checks.py'),
 'data/08-skeleton-verification_results.json': ('research1', 'verification_results.json'),
 'data/09-core-finite_checks.json': ('research', 'data/finite_checks.json'),
 'data/11-raw-orders-finite_checks_results.txt': ('lower1', 'finite_checks_results.txt'),
 'data/12-singular-finite_checks.json': ('lower', 'data/finite_checks.json')}

def digest(b):
    return hashlib.sha256(b).hexdigest()

def require(test, message):
    if not test:
        raise ValueError(message)

def exact(a,b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple):
        return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def git(repo,*args):
    return subprocess.check_output(['git','-C',str(repo),*args],timeout=60)

def blob(repo,commit,path):
    return git(repo,'show',commit+':'+path)

def run(repo):
    repo=Path(repo).resolve()
    require(git(repo,'rev-parse',PLACEMENT).decode().strip()==PLACEMENT,'placement object')
    require(git(repo,'rev-parse',ARRIVAL).decode().strip()==ARRIVAL,'arrival object')
    parent=git(repo,'rev-parse',PLACEMENT+'^').decode().strip()
    sources={};archive_receipts=[]
    for a in ARCHIVES:
        path='docs/incoming/'+a['archive']; b=blob(repo,ARRIVAL,path)
        require(digest(b)==a['sha256'],'archive pin '+path)
        actual=[];seen=set()
        with zipfile.ZipFile(io.BytesIO(b)) as z:
            require(sum(i.file_size for i in z.infolist())<64*1024*1024,'ZIP size limit')
            for i in z.infolist():
                p=PurePosixPath(i.filename)
                require(not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename and bool(p.parts),'unsafe member')
                require(i.filename not in seen,'duplicate member');seen.add(i.filename)
                require(not stat.S_ISLNK(i.external_attr>>16),'symlink member')
                if i.is_dir():
                    continue
                require(i.file_size<16*1024*1024,'member size limit')
                data=z.read(i)
                actual.append({'path':i.filename,'size':len(data),'sha256':digest(data)})
                sources[(a['label'],i.filename)]=data
        require(exact(sorted(actual,key=lambda r:r['path']),sorted(a['members'],key=lambda r:r['path'])),'full member pin '+a['label'])
        archive_receipts.append({'archive':path,'label':a['label'],'sha256':digest(b),'members':sorted(actual,key=lambda r:r['path'])})
    placed=git(repo,'ls-tree','-r','--name-only',PLACEMENT,'--',TARGET).decode().splitlines()
    require(placed==sorted(TARGET+'/'+p for p in MAPPING),'complete placed inventory')
    used=set();transfers=[]
    for path,(label,member) in sorted(MAPPING.items()):
        m='surreal_well_orders/'+member;k=(label,m);target=TARGET+'/'+path
        require(k not in used,'duplicate source placement');used.add(k)
        b=blob(repo,PLACEMENT,target)
        require(b==sources[k],'changed delivered bytes '+target)
        transfers.append({'target':target,'source_label':label,'member':m,'bytes':len(b),'sha256':digest(b),'git_blob':git(repo,'rev-parse',PLACEMENT+':'+target).decode().strip()})
    changes=[line.split('\t',1) for line in git(repo,'diff-tree','--no-commit-id','--name-status','-r',PLACEMENT).decode().splitlines()]
    expected=[['A',TARGET+'/'+p] for p in MAPPING]+[['D','docs/incoming/'+a['archive']] for a in ARCHIVES]
    require(sorted(changes)==sorted(expected),'placement scope changed')
    omitted=[]
    for (label,path),b in sorted(sources.items()):
        if (label,path) in used:continue
        if path.endswith('.pdf'): reason='delivery PDF deliberately not staged; no merged PDF staged at this commit'
        elif path.endswith('.tex'):reason='complementary source manuscript retained in arrival history, pending merged write'
        elif '/README.' in path:reason='delivery README retained in arrival history, pending merged guide'
        else:
            require(path.endswith('/SHA256SUMS.txt'),'unexpected omitted member')
            reason='original delivery manifest retained in arrival history'
        omitted.append({'label':label,'member':path,'sha256':digest(b),'reason':reason})
    require(len(sources)==29 and len(transfers)==16 and len(omitted)==13,'accounting')
    msg=git(repo,'show','-s','--format=%B',PLACEMENT).decode()
    for phrase in ['Staged (16 files)', 'bytes unchanged, rewritten at the write', 'Not staged (they survive in 4e270aa46)', 'which the write merges into']:
        require(phrase in msg,'staging disclosure changed')
    base=sources[('lower1','surreal_well_orders/surreal_well_orders.tex')]
    text=base.decode()
    return {'arrival':ARRIVAL,'placement':PLACEMENT,'placement_parent':parent,'target':TARGET,
      'checker_sha256':digest(Path(__file__).read_bytes()),'archives':archive_receipts,'transfers':transfers,
      'unstaged_members':omitted,'commit_message_sha256':digest(msg.encode()),
      'checks':{'archives_authenticated':4,'all_original_members_authenticated':29,'distinct_original_member_hashes':len({digest(b) for b in sources.values()}),
        'byte_identical_transfers':16,'omissions_disclosed':13,'added_files':16,'removed_archives':4,'new_or_modified_math_source_lines':0,
        'base_article_lines':len(text.splitlines()),'base_article_label_occurrences':len(re.findall(r'\\label(?:\[[^\]]*\])?\{([^}]+)\}',text)),
        'base_article_is_entire_source11':True,'readme_is_unchanged_source11_delivery_readme':True,
        'merged_pdf_present':False,'author_programs_executed':0,'article_builds':0},
      'conclusion':'PASS for authenticated source staging only; synthesis of the three complementary source manuscripts remains pending at this pinned commit',
      'scope':'byte identity and complete staging inventory, not a new theorem proof, a completed merge claim, a PDF audit or a rerun of unchanged author suites'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',required=True,type=Path);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path)
    a=p.parse_args();r=run(a.repo)
    if a.expect:
        require(exact(r,json.loads(a.expect.read_text())),'saved receipt differs (including exact scalar types)')
    if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','checks':r['checks']},sort_keys=True))
if __name__=='__main__':main()
