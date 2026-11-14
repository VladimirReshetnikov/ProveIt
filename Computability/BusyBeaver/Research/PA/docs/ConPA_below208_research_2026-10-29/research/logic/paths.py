from pathlib import Path
import os
HERE=Path(__file__).resolve().parent
INPUTS=HERE/"inputs"
OUT=Path(os.environ.get("LOGIC_RESEARCH_OUTPUT",str(HERE/"replay"))).resolve()
OUT.mkdir(parents=True,exist_ok=True)
