"""Independently replay the normal and port-incidence proofs in this delivery."""
import json
from pathlib import Path
import sys

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))

from fastunknot.interval_incidence import verify_port_incidence_certificate
from fastunknot.normal_components import verify_normal_surface_certificate


def main():
    normal_path = FAST / "normal_orbit_research/examples/fibonacci32_certificate.json"
    normal = json.loads(normal_path.read_text())
    if not verify_normal_surface_certificate(
        normal["triangulation"], normal["coordinates"], normal["certificate"]
    ):
        raise RuntimeError("The delivered normal-surface certificate was rejected")
    incidence_path = FAST / "results/interval_incidence_cert_1024_4.json"
    incidence = json.loads(incidence_path.read_text())
    if not verify_port_incidence_certificate(
        incidence["size"], incidence["pairings"], incidence["ports"], incidence["certificate"]
    ):
        raise RuntimeError("The delivered port-incidence certificate was rejected")
    print(json.dumps({"normal_certificate": "accepted", "incidence_certificate": "accepted"}))


if __name__ == "__main__":
    main()
