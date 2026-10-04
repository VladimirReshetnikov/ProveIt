"""Read-only page-raster review: decode PNGs and compose review contact sheets."""
from pathlib import Path
from PIL import Image,ImageDraw,ImageStat
import hashlib,json
base=Path('/workspace/shared/report67-release-independent-review-20261004')
rows=[]
paths=sorted((base/'full-build/pages').glob('*.png'))
for offset in range(0,len(paths),4):
    sheet=Image.new('RGB',(1360,1840),'#cccccc');draw=ImageDraw.Draw(sheet)
    for j,path in enumerate(paths[offset:offset+4]):
        with Image.open(path) as original:
            original.load();assert original.size==(1020,1320)
            gray=original.convert('L');h=gray.histogram();assert sum(h[:230])>1000
            rows.append({'page':path.name,'size':list(original.size),'dark_pixels':sum(h[:230]),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
            thumb=original.copy();thumb.thumbnail((660,870))
        x=(j%2)*680+10;y=(j//2)*920+30
        sheet.paste(thumb,(x,y));draw.text((x,y-20),path.name,fill='black')
    sheet.save(base/('contact-'+str(offset+1).zfill(2)+'-'+str(offset+4).zfill(2)+'.png'))
(base/'RASTER_DECODE_RECEIPT.json').write_text(json.dumps({'status':'PASS','pages':rows},indent=2)+'\n')
print('Decoded all',len(rows),'pages and made six contact sheets')
