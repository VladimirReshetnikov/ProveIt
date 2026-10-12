"""Run with PYTHONPATH=src from this delivery's root."""
import argparse,json
from pathlib import Path
from report91_adapter import translate
from gauge_cuts import compile_grammar
from checker import verify_packet
p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--threshold',type=int,default=3)
a=p.parse_args();original=json.loads(a.source.read_text());g=translate(original,a.threshold)
packet=compile_grammar(g);print(json.dumps(verify_packet(packet,g),indent=2))
