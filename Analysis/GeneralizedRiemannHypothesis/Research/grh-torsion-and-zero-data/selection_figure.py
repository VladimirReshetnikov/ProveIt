"""Create the shell-budget figure and check the example used in the paper."""
from fractions import Fraction
from pathlib import Path

from check_minimax import least_blocking_m


def minimum_charge(p, h, epsilon):
    """Invert the floor sum using the base-p digits of m // (p - 1)."""
    size = (p - 1) * p ** (h - 1)
    available = (epsilon.numerator * size) // (epsilon.denominator * (p - 1))
    # The score for digits c_j is sum c_j (j+1) p^j.
    value = 0
    for j in reversed(range(h - 1)):
        place = p ** j
        weight = (j + 1) * place
        digit = min(p - 1, available // weight)
        available -= digit * weight
        value += digit * place
    return Fraction((p - 1) * (value + 1), size)


def budget_curve(p, tolerance, last):
    result = []
    total = Fraction()
    for h in range(1, last + 1):
        term = minimum_charge(p, h, tolerance)
        if h <= 30:
            assert term * ((p - 1) * p**(h-1)) == least_blocking_m(p, h, tolerance)
        total += term
        result.append(total)
    return result


def main():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(7.0, 2.9), layout="constrained")
    for color, den in [("#b95730", 4), ("#006e70", 8), ("#506a99", 16)]:
        tolerance = Fraction(1, den)
        costs = budget_curve(2, tolerance, 512)
        ax.plot(range(1, 513), [float(x) for x in costs], color=color,
                label=f"tolerance 1/{den}", lw=1.9)
        if den == 8:
            n = next(i for i, x in enumerate(costs, 1) if x > 3)
            assert n == 372
            assert Fraction(29998, 10000) < costs[370] < 3 < costs[371] < Fraction(30003, 10000)
            print("First guaranteed shell at p=2, B=3, tolerance=1/8:", n)
            print("Minimum blocking budgets for H=371 and H=372:", *(float(x) for x in costs[370:372]))
            ax.scatter([n], [3], color=color, zorder=4, s=24)
            ax.annotate("H = 372", xy=(n, 3), xytext=(100, 3.24), fontsize=8,
                        arrowprops={"arrowstyle": "-", "color": color})
    ax.axhline(3, color="#64717a", lw=.9, ls="--", zorder=0)
    ax.set_xscale("log", base=2)
    ax.set_xticks([1, 4, 16, 64, 256, 512], ["1", "4", "16", "64", "256", "512"])
    ax.set(xlabel="Last shell exponent H", ylabel="Minimum blocking budget",
           xlim=(1, 530))
    ax.spines[["top", "right"]].set_visible(False)
    ax.grid(axis="y", linewidth=.45, color="#d5dadc")
    ax.legend(frameon=False, ncol=3, loc="lower right", fontsize=8)
    fig.savefig(Path(__file__).with_name("selection_budget.pdf"))


if __name__ == "__main__":
    main()
