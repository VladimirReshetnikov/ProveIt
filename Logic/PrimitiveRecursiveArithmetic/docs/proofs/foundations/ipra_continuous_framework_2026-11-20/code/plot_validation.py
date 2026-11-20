"""Create a publication figure from the exact validation receipt."""
from pathlib import Path
import json
from fractions import Fraction
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / "validation" / "results.json").read_text())
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "pdf.fonttype": 42, "ps.fonttype": 42})
fig, axes = plt.subplots(1, 3, figsize=(10.2, 3.2))
blue, amber = "#145b87", "#b55b12"

rows = [r for r in data["logic"] if r["problem"] == "asymmetric minimum"]
axes[0].semilogy([r["k"] for r in rows], [float(Fraction(r["error"])) for r in rows],
                 "o-", color=blue, label="actual error")
axes[0].semilogy([r["k"] for r in rows], [float(Fraction(r["bound"])) for r in rows],
                 "s--", color=amber, label="proved budget")
axes[0].set(title="Continuous formula", xlabel="net precision k", ylabel="absolute error")

rows = data["ode"]
axes[1].semilogy([r["n"] for r in rows], [r["error_upper"] for r in rows],
                 "o-", color=blue)
axes[1].semilogy([r["n"] for r in rows], [r["bound"] for r in rows],
                 "s--", color=amber)
axes[1].set(title="Rounded Euler solution", xlabel="output precision n")

rows = data["cauchy"]
axes[2].loglog([r["N"] for r in rows], [r["error_upper"] for r in rows],
               "o-", color=blue)
axes[2].loglog([r["N"] for r in rows], [r["bound"] for r in rows],
               "s--", color=amber)
axes[2].set(title="Polygon Cauchy transform", xlabel="subdivisions per edge N")
for ax in axes:
    ax.grid(True, which="major", color="#dce2e7", linewidth=0.6)
axes[0].legend(frameon=False, fontsize=8)
fig.tight_layout(pad=1.3)
out = ROOT / "figures"
out.mkdir(exist_ok=True)
fig.savefig(out / "validation.pdf", bbox_inches="tight")
fig.savefig(out / "validation.png", dpi=170, bbox_inches="tight")
print("Saved validation figure")
