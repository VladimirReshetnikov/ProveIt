#!/usr/bin/env python3
"""Restore the attributed design ledgers from four exact pinned delivery ZIPs."""
from pathlib import Path
import argparse,csv,hashlib,io,json,re,zipfile
import machine_classes as mc
HERE=Path(__file__).resolve().parent
PIN='793c68737d94bffa4e32a75bce6cc8058d6d22f0'
ARCHIVES={
 'pa194_comparison_and_new_designs_2026-11-15.zip':'cccacef93822114242f28df0c75a347f4e2fdd42',
 'pa194_gd_research_2026-11-14.zip':'cf727bb42b0945aacbfe3cb0e847abe71864809d',
 'pa194_lcfast_tagged_research_2026-11-14.zip':'4f869ab3d2e0373fcd229d182ebeade913d7b4dd',
 'pa194_loop_return_2026-11-14.zip':'fdad64ce2edc7d429356cb0e72d707cc717a9c04'}
def write(name,rows):
 (HERE/(name+'.json')).write_text(json.dumps(rows,indent=2)+'\n')
 fields=list(dict.fromkeys(k for r in rows for k in r))
 with (HERE/(name+'.csv')).open('w',newline='')as f:
  w=csv.DictWriter(f,fieldnames=fields);w.writeheader();w.writerows(rows)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--archive-dir',type=Path,required=True);a=ap.parse_args()
 zs={};ident=[]
 for name,blob in ARCHIVES.items():
  b=(a.archive_dir/name).read_bytes();assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
  zs[name]=zipfile.ZipFile(io.BytesIO(b));ident.append(dict(name=name,bytes=len(b),git_blob_sha=blob,sha256=hashlib.sha256(b).hexdigest(),source_url=f'https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/{PIN}/docs/incoming/{name}'))
 sf=zs[next(iter(ARCHIVES))];prefix='pa194_sf_research/comparison/'
 base=list(csv.DictReader(io.StringIO(sf.read(prefix+'frontier194_annotated.csv').decode())))
 named=[r for r in base if 'principal'in r['role']or'supplementary'in r['role']];assert len(named)==74
 additions=[
  (0,'pa194_sf_research/composites/machines/PA194AX11H_SF/machine.tm','PA194AX11H_SF','Selector plus two guarded physical shortcuts on exact AX11H; 57918-step startup.'),
  (0,'pa194_sf_research/composites/machines/PA194LC_AX11H_SF/machine.tm','PA194LC_AX11H_SF','Same compatible selector/shortcut composition on LC_AX11H; 57918-step startup.'),
  (1,'pa194_gd_research_2026-11-14/machines/GD/machine.tm','PA194GD','Explicit binder U(c,h), diagonal Gamma(D), no-push MP, sum guard; 58154-step startup.'),
  (1,'pa194_gd_research_2026-11-14/machines/GDH/machine.tm','PA194GDH','Same independent binder/diagonal source with cache-only guard; 57922-step startup.'),
  (1,'pa194_gd_research_2026-11-14/machines/GDHS/machine.tm','PA194GDHS','Same GDH source with symmetric physical comparison; 57768-step startup.'),
  (2,'pa194_lcfast_tagged_research_2026-11-14/machines/PA194LCAX11GHF/machine.tm','PA194LCAX11GHF','Loop continuation reassociation plus two exact physical shortcuts on AX11GH.'),
  (2,'pa194_lcfast_tagged_research_2026-11-14/machines/PA194LCAX11GHSF/machine.tm','PA194LCAX11GHSF','Loop continuation reassociation plus two exact physical shortcuts on AX11GHS.'),
  (3,'pa194_loop_return_2026-11-14/machines/PA194LCG/machine.tm','PA194LCG','GH loop-continuation source with third guarded return shortcut at native 190/1.'),
  (3,'pa194_loop_return_2026-11-14/machines/PA194LCGS/machine.tm','PA194LCGS','GHS loop-continuation source with third guarded return shortcut at native 190/1.')]
 for idx,member,name,mechanism in additions:
  archive=list(ARCHIVES)[idx];b=zs[archive].read(member);cl=mc.classify(b)
  named.append(dict(table_class=cl['table'],states=194,reachable=194,name=name,role='reported principal construction',mechanism=mechanism,claim_scope='Attributed supplied written mathematical claim; absolute AX11H calibration inherited, no new kernel theorem inferred by inventory.',new_vs_filed=True,current_source='docs/incoming/'+archive+'!'+member,local_representative='census/representatives/'+cl['table']+'.tm',sha256=hashlib.sha256(b).hexdigest()))
 assert len(named)==len({r['table_class']for r in named})==83
 for r in named:r['local_representative']='census/representatives/'+r['table_class']+'.tm'
 write('named_designs83',sorted(named,key=lambda r:r['name']))
 families=list(csv.DictReader(io.StringIO(sf.read(prefix+'family_comparison.csv').decode())));assert len(families)==27
 families += [
  dict(family='Selector plus acceleration',designs='PA194AX11H_SF; PA194LC_AX11H_SF',recurring_behavior='Preserves exact AX11H/LC_AX11H source protocol; combines compatible history selector and physical speedups.',physical_change='Selector plus two exact three-to-one shortcuts.',proof_obligation='Check shortcut invariants on selector intermediate; direct bounded halting transfer with 3t; inherited AX11H calibration.'),
  dict(family='Loop continuation plus two shortcuts',designs='PA194LCAX11GHF; PA194LCAX11GHSF',recurring_behavior='Preserves GH/GHS resolved source graphs while changing 61 constructor-loop occurrences and 305 primitive addresses.',physical_change='Loop reassociation and two physical accelerations.',proof_obligation='Complete source-frame contracts and inter-frame clock; Theta(t)=13t^2+715t+58624; inherited GH/GHS and AX11H calibration.'),
  dict(family='Loop return acceleration',designs='PA194LCG; PA194LCGS',recurring_behavior='Same GH/GHS source and loop reassociation; adds exact return at native190/1.',physical_change='Third guarded three-step path replaced by one step.',proof_obligation='Unique predecessor invariant and full configuration endpoint; Theta(t)=13t^2+1173t+61160; inherited calibration.'),
  dict(family='Independent binder and diagonal operands',designs='PA194GD; PA194GDH; PA194GDHS',recurring_behavior='Ten-entry AX uses explicit binder c in U(c,h), independent D=d+x in Gamma(D), original distribution premise order and no-push MP.',physical_change='134+69-9 or 135+69-10 controls with alternative halt detectors.',proof_obligation='Independent all-store command compilers, diagonal selector, complete physical frames/startup and inherited revised AX11H calibration.')]
 assert len(families)==31;write('family_comparison31',families)
 # The SF packet's older 93-delivery ledger grouped 87 filed plus six then
 # incoming packets. At this pin those six have moved into PA/docs. Derive
 # the 93 filed locations directly from the exact current pinned README.
 packets=[]
 pattern=re.compile(r'^\| \[`([^`]+)`\]\(([^)]+)\) \| ([^|]+) \| ([^|]+) \| (.*?) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \|$')
 for line in(HERE/'catalog/README.md').read_text().splitlines():
  m=pattern.match(line)
  if m:
   name,location,arrival,wrapper,description,*counts=m.groups()
   packets.append(dict(packet=name,location='Computability/BusyBeaver/Research/PA/docs/'+location.rstrip('/'),arrival=arrival.strip(),wrapper=wrapper.strip(' `'),reported_result=description,scope='Filed packet summary attributed to exact pinned PA/docs/README; not an independent consistency proof audit.',source='filed_catalog'))
 assert len(packets)==93
 descriptions=['SF selector and two accelerations on AX11H and LC_AX11H; comparative inventory.','Independent explicit generalization binder and Gamma(D) diagonal: GD,GDH,GDHS.','Loop reassociation plus two shortcuts on GH/GHS; tagged architecture research.','GH/GHS loop return acceleration at native190/1.']
 for (name,blob),description in zip(ARCHIVES.items(),descriptions):
  packets.append(dict(packet=name,location='docs/incoming/'+name,arrival='2026-11-15'if'2026-11-15'in name else'2026-11-14',wrapper='pa194_sf_research'if name.startswith('pa194_comparison')else name[:-4],reported_result=description,scope='Current pinned incoming archive; attributed report claims with exact literal identity.',source='current_incoming'))
 write('packet_ledger97',packets)
 (HERE/'incoming_identities.json').write_text(json.dumps(dict(pin=PIN,archives=ident),indent=2)+'\n')
 if(HERE/'census/frontier194.json').is_file():
  frontier=json.loads((HERE/'census/frontier194.json').read_text())
  filed_keys={r['table_class']for r in csv.DictReader((HERE/'catalog/MACHINES.tsv').open(),delimiter='\t')}
  mapping={r['table_class']:r for r in base};mapping.update({r['table_class']:r for r in named});annotated=[]
  for cl in frontier:
   r=mapping.get(cl['table_class'],dict(table_class=cl['table_class'],name='Research auxiliary '+cl['table_class'][:12],role='research auxiliary',mechanism='Additional complete physical research table recognized in pinned incoming archives.',claim_scope='No calibrated consistency theorem assigned by this inventory.',new_vs_filed=True,current_source=cl['occurrences'][0]['path'])).copy()
   r['attributed_original_locator']=r.get('current_source','')
   r['current_source']=cl['occurrences'][0]['path']
   r['new_vs_filed']=cl['table_class']not in filed_keys
   r.update(states=194,reachable=194,local_representative='census/'+cl['representative'],sha256=cl['sha256']);annotated.append(r)
  assert len(annotated)==520
  write('frontier520_annotated',annotated)
  write('named_designs83',sorted([r for r in annotated if'principal'in r['role']or'supplementary'in r['role']],key=lambda r:r['name']))
 print(json.dumps(dict(named_designs=83,families=31,deliveries=97,pin=PIN),indent=2))
if __name__=='__main__':main()
