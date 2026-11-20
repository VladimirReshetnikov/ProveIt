"""Run inside lake env. Appended commands audit the actual compiled declarations."""
from pathlib import Path
import sys
import tempfile

from verify import run

AUDIT = {
    "AffineCarry": ["Packet.Affine.closedCarry"],
    "Detour": ["ParameterDetour.clearanceAfterMove","ParameterDetour.verticalInteger"],
    "Forest": ["IPRAForest.restrict_extend","IPRAForest.extend_restrict"],
    "ForestObject": ["IPRAForestObject.liftEdgeImp"],
    "ObjectRewrite": ["Packet.ObjectRewrite.compile","Packet.ObjectRewrite.closedSquare"],
    "PairBounds": ["PairBounds.lower_of_mix","PairBounds.extremal_bound"],
    "PairBoundsIPRA": ["PairBoundsIPRA.closed_mix_lower"],
    "Resonance": ["Resonance.logObstruction","Resonance.matchingCofactors"],
    "ResonanceObject": ["Packet.ResonanceObject.closedExceptional","Packet.ResonanceObject.closedFirstLog"],
    "Transport": ["PresentedTransport.rewrite_sound"],
}
sources = sorted(Path(sys.argv[1]).glob("*.lean"))
if set(f.stem for f in sources) != set(AUDIT):
    raise SystemExit("the source inventory and axiom audit disagree")
with tempfile.TemporaryDirectory() as tmp:
    for src in sources:
        code = src.read_text()
        if "sorry" in code or "admit" in code:
            raise SystemExit(f"placeholder in {src.name}")
        # Preserve the checked source bytes and add only diagnostic commands.
        checked = Path(tmp)/src.name
        already = {line.split()[-1].split(".")[-1] for line in code.splitlines()
                   if line.strip().startswith("#print axioms ")}
        checks = "\n".join("#print axioms " + n for n in AUDIT[src.stem]
                           if n.split(".")[-1] not in already)
        checked.write_text(code+"\n"+checks+"\n")
        run(["lean",str(checked)])
print(f"\nAll {len(sources)} Lean files passed.",flush=True)
