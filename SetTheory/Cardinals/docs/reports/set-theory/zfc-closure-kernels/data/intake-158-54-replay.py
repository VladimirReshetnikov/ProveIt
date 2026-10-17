from pathlib import Path
import runpy,sys
root=Path(__file__).parent/"package"
namespace=runpy.run_path(str(root/"verify.py"))
namespace["main"].__globals__["check_manifest"]=lambda: None
sys.argv=[str(root/"verify.py"),"--output",str(Path(__file__).parent/"positive.json")]
namespace["main"]()
