"""Plot limiting rank probabilities for a square isotropic block over F_2."""
from math import prod
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.ticker import PercentFormatter


def probabilities(q, c, d):
    Q = 1/q
    # With q=2, the discarded tail changes a product by less than 2^-99.
    normal = prod(1-Q**j for j in range(1, d+1))
    symplectic = Q**(c*d+d*(d+1)//2)/normal / prod(1+Q**j for j in range(c+1, 101))
    uniform = Q**(d*(d+c))/normal * prod(1-Q**j for j in range(c+d+1, 101))
    return symplectic, uniform


def main():
    probs = [probabilities(2, 0, d) for d in range(4)]
    series = [[row[j] for row in probs] for j in range(2)]
    for v in series:
        v.append(1-sum(v))
    fig, ax = plt.subplots(figsize=(6.9, 2.45), layout="constrained")
    for j, (data, label, color) in enumerate(zip(series, ("Isotropic block", "Uniform matrix"),
                                                  ("#0D6862", "#A84F32"))):
        ax.bar([d+(j-0.5)*0.31 for d in range(5)], data, width=.29,
               label=label, color=color, zorder=2)
    ax.set_xticks(range(5), ["0", "1", "2", "3", "4+"])
    ax.set_xlabel("Row rank deficiency")
    ax.set(ylabel="Limiting probability", ylim=(0, 0.64))
    ax.yaxis.set_major_formatter(PercentFormatter(1, decimals=0))
    ax.spines[["top", "right", "left"]].set_visible(False)
    ax.tick_params(length=0)
    ax.grid(axis="y", color="#d5dcdc", lw=.6)
    ax.legend(frameon=False, loc="upper right")
    fig.savefig(Path(__file__).with_name("rank_laws.pdf"), metadata={"CreationDate": None})
    for j in range(2):
        print("  ".join(f"{a:.7f}" for a in series[j]))
    print(f"Limiting total variation = {series[1][1]-series[0][1]:.9f}")


if __name__ == "__main__":
    main()
