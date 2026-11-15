#!/usr/bin/env python3
"""Build readable ledgers from the exact census and attributed source indexes."""
import argparse, csv, hashlib, json, re, subprocess
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
PIN='603c58ca3bd6bf3222fcfc4e308e6b079f65d573'
ROOT_URL='https://github.com/VladimirReshetnikov/ProveIt/blob/'+PIN+'/'

def write_csv(path,items):
    keys=list(items[0])
    with path.open('w',newline='')as f:
        w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(items)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('repo',type=Path);ap.add_argument('incoming',type=Path)
    args=ap.parse_args()
    ancestor=args.incoming/'pa194_ax11g_research_2026-11-14/pa194_ax11g_research_2026-11-14/comparison/all_194_designs.json'
    old={x['canonical_class']:x for x in json.loads(ancestor.read_text())}
    ledger=json.loads((HERE/'frontier194.json').read_text())
    descriptions={
      '7d1e14a2a3a3':('PA194AX11G','reported principal construction','Eleven-entry AX with a fourth operand and explicit-operand generalization binder; original sum guard.'),
      'aefc70c9bf99':('PA194GH','reported principal construction','Explicit-operand generalizer combined with cache-only Shift and the three-field AX protocol; repeated by two current packets.'),
      'ac203041f369':('PA194GHS','reported principal construction','GH command semantics implemented by the symmetric physical comparison; 135 fixed controls + 67 readers - 8 folds.'),
      '3c217a206073':('PA194AX11QH4L','reported principal construction','Reassociates the recurring four-increment decoder to the left in the AX11QH source; adds one reader and one contextual fold.'),
      'bd890297a365':('PA194AX11QH4R','reported principal construction','Right-associated four-increment decoder in the unchanged AX11QH source; relative bounded-trace preservation.'),
      '6760942c0ee7':('AX11QH4R+B auxiliary','research auxiliary','Additional local selector/decoder composition supplied in the QH4 packet; not one of its two principal constructions.'),
      '887a47f7c32e':('AX11QH4L+B auxiliary','research auxiliary','Additional local selector/decoder composition supplied in the QH4 packet; separate from its principal left-associated table.'),
      'ef2f684a705d':('B+4L auxiliary','research auxiliary','Additional local composition included as a QH4 research input; no principal calibration is counted here.'),
    }
    annotations=[]
    for c in ledger:
        h=c['canonical_class']
        if h in old:
            a=old[h];name,category,mechanism=a['name'],a['category'],a['mechanism']
            origin='Inherited mechanism annotation, reconciled by exact canonical tuple; historical proof claims not all independently rerun.'
        elif h[:12] in descriptions:
            name,category,mechanism=descriptions[h[:12]];origin='Current incoming packet, matched to the exact table.'
        else:
            p=Path(c['representative']);name='GH neutral '+p.stem.replace('edit_','edit ')
            category='research auxiliary';mechanism='A same-count neutral-edit research table in the GH packet; graph identity alone does not certify its blank-start calibration.'
            origin='Current incoming research directory.'
        annotations.append(dict(name=name,category=category,mechanism=mechanism,canonical_class=h,
                                strong_class=c['strong_class'],table_file=c['table_file'],table_sha256=c['sha256'],
                                representative=c['representative'],evidence_scope=origin))
    annotations.sort(key=lambda x:(x['category'],x['name']))
    (HERE/'all_194_designs.json').write_text(json.dumps(annotations,indent=2)+'\n')
    write_csv(HERE/'all_194_designs.csv',annotations)
    packets=[]
    path=args.repo/'Computability/BusyBeaver/Research/PA/docs/README.md'
    for line in path.read_text().splitlines():
        m=re.match(r'\| \[`([^`]+)`\]\(([^)]+)\) \| ([^|]+) \| ([^|]+) \| (.*?) \| (\d+) \|',line)
        if not m:continue
        name,_,arrival,wrapper,claim,placed=m.groups()
        locator='Computability/BusyBeaver/Research/PA/docs/'+name+'/'
        packets.append(dict(packet=name,location='filed directory',arrival=arrival.strip(),reported_result=claim.strip(),source=locator))
    assert len(packets)==82,len(packets)
    extra={
      'pa194_ax11g_research_2026-11-14':'AX11G: explicit AX binder with eleven-entry/four-field AX. Reports no sub-194 result and no completed absolute iPRA calibration.',
      'pa194_ax11h_research_2026-11-14':'New delivery under an existing name. AX11H table repeats the filed class; adds audits and research material. No sub-194 or absolute iPRA result.',
      'pa194_ax11qh4_research_2026-11-14':'AX11QH4L and AX11QH4R: two decoder reassociations, each 194 states, with bounded relative halting transfers. Three additional local auxiliary tables.',
      'pa194_frontier_2026-11-14':'AX11G and GH constructions, both also delivered separately; joint frontier audit and reduction searches. No smaller machine or absolute calibration.',
      'pa194gh_research_2026-11-14':'GH and symmetric GHS, plus eight same-count neutral-edit research tables and new bounded reduction searches. No accepted sub-194 machine.'}
    for p in sorted((args.repo/'docs/incoming').glob('*.zip')):
        packets.append(dict(packet=p.name,location='current incoming ZIP',arrival='2026-11-14',reported_result=extra[p.stem],source=str(p.relative_to(args.repo))))
    assert len(packets)==87
    (HERE/'packet_ledger87.json').write_text(json.dumps(packets,indent=2)+'\n');write_csv(HERE/'packet_ledger87.csv',packets)
    # All source table bytes and incoming archives are bound to the Git snapshot.
    tree=subprocess.check_output(['git','-C',str(args.repo),'ls-tree','-r',PIN,
           'Computability/BusyBeaver/Research/PA','docs/incoming'],text=True).splitlines()
    integrity=[]
    for line in tree:
        meta,name=line.split('\t',1)
        if not(name.endswith('.tm')or(name.startswith('docs/incoming/')and name.endswith('.zip'))):continue
        expected=meta.split()[2];data=(args.repo/name).read_bytes()
        actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert actual==expected,(name,actual,expected)
        integrity.append(dict(path=name,git_blob=actual,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
    (HERE/'source_integrity.json').write_text(json.dumps(integrity,indent=2)+'\n')
    info=dict(source_commit=PIN,filed_packets=82,current_incoming_deliveries=5,total_deliveries=87,
              frontier_classes=len(annotations),categories=dict(Counter(x['category']for x in annotations)),
              source_payloads_checked=len(integrity),mechanism_annotation_source=str(ancestor.relative_to(args.incoming)),
              source_url=ROOT_URL+'Computability/BusyBeaver/Research/PA/docs/README.md')
    (HERE/'ledger_summary.json').write_text(json.dumps(info,indent=2)+'\n');print(json.dumps(info,indent=2))
if __name__=='__main__':main()
