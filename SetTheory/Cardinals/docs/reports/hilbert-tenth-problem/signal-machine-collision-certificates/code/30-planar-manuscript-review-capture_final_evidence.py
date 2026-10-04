"""Read-only final PDF/source binding, render equivalence and geometry scan."""
from pathlib import Path
import hashlib,json,re
import pdfplumber
from PIL import Image
R=Path('/workspace/shared/planar-signal-report60-release-20261004')
B=Path('/workspace/shared/report60-build-e-20261004')
O=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected=json.loads((R/'manuscript/MANUSCRIPT_PINS.json').read_text())
actual={n:sha(R/'manuscript'/n) for n in expected}
if actual!=expected:raise RuntimeError('source pins mismatch')
flat=(R/'manuscript/Report60.tex').read_text()
for name in ['physical.tex','geometry.tex','arithmetic.tex','evidence.tex']:
 flat=flat.replace('\\input{'+name+'}\n',(R/'manuscript'/name).read_text())
if flat!=(R/'Report60.tex').read_text():raise RuntimeError('flattening mismatch')
if re.search(r'(?<!\\)\b(?:quad|qquad)\b',flat):raise RuntimeError('literal spacing command')
if '1+\\lfloor\\log_2 b\\rfloor' not in flat:raise RuntimeError('E1 correction missing')
record={'source_pins':actual,'source_manifest_sha256':sha(R/'manuscript/MANUSCRIPT_PINS.json'),'standalone_sha256':sha(R/'Report60.tex'),'standalone_exact_flattening':True,'pdf_sha256':sha(B/'Report60.pdf'),'pdf_pages':[],'render_sha256':{},'all_render_images_match_build':True}
with pdfplumber.open(B/'Report60.pdf') as doc:
 for i,page in enumerate(doc.pages,1):
  text=page.extract_text() or ''
  bad=[c['text'] for c in page.chars if c['x0']<0 or c['x1']>page.width+.1 or c['top']<0 or c['bottom']>page.height+.1]
  header='Report 60' in text and '4 October 2026' in text
  if bad or not header:raise RuntimeError('PDF geometry or header failure '+str(i))
  name=f'page-{i:02}.png';p=O/'final-pages'/name
  if sha(p)!=sha(B/'pages'/name):raise RuntimeError('render mismatch '+name)
  im=Image.open(p).convert('L'); header_dark=sum(x<128 for x in im.crop((0,30,im.width,80)).getdata())
  record['pdf_pages'].append({'page':i,'characters':len(page.chars),'width_pt':page.width,'height_pt':page.height,'min_x_pt':min(c['x0'] for c in page.chars),'max_x_pt':max(c['x1'] for c in page.chars),'out_of_page_characters':bad,'both_running_header_fields':header,'header_dark_pixels':header_dark})
  record['render_sha256'][name]=sha(p)
log=(B/'compile-3.log').read_text()
record['overfull_boxes']=len(re.findall(r'Overfull \\[hv]box',log))
record['underfull_boxes']=len(re.findall(r'Underfull \\[hv]box',log))
record['unresolved_references']='undefined' in log.lower()
record['missing_character_warning']='Missing character' in log
if record['overfull_boxes'] or record['unresolved_references'] or record['missing_character_warning']:raise RuntimeError('compile diagnostics')
record['status']='PASS'
(O/'FINAL_EVIDENCE.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','pages':len(record['pdf_pages']),'pdf_sha256':record['pdf_sha256'],'overfull_boxes':record['overfull_boxes'],'underfull_boxes':record['underfull_boxes'],'all_render_images_match_build':True},sort_keys=True))
