import seaborn
import matplotlib.pyplot as plt
import pandas as pd
import sys
import json
import re
from collections import Counter


def flatten(samples):
    cats = samples[1].keys()
    flat_samples = dict([(k, []) for k in cats])
    flat_samples.update({f"lambda{i}": [] for i in range(4)})
    for s in samples:
        for c in cats:
            if c != "lambda":
                flat_samples[c].append(s[c])
            else:
                for i, v in enumerate(s["lambda"]):
                    flat_samples[f"lambda{i}"].append(v)

    return flat_samples


with open("hrm-samples.json") as fh:
    samples = json.load(fh)
    samples = flatten(samples)
    plot_vars = ["mu", "beta", "lambda0", "lambda1", "lambda2", "lambda3"]

    df = pd.DataFrame({k: v for k, v in samples.items() if k in plot_vars})

    # Histogram plots
    fig, axes = plt.subplots(3, 2, figsize=(12, 10))
    axes = axes.flatten()

    plot_vars = ["mu", "beta", "lambda0", "lambda1", "lambda2", "lambda3"]

    for i, var in enumerate(plot_vars):
        seaborn.histplot(samples[var], ax=axes[i], kde=True)
        axes[i].set_title(var)
        if var.startswith("lambda"):
            axes[i].set_xlim(0, 1)
        else:
            axes[i].set_xlim(0)

    plt.tight_layout()

    # Trace plots
    fig2, axes2 = plt.subplots(3, 2, figsize=(12, 10))
    axes2 = axes2.flatten()

    for i, var in enumerate(plot_vars):
        axes2[i].plot(samples[var], linewidth=0.5, alpha=0.7)
        axes2[i].set_title(f"Trace: {var}")
        axes2[i].set_xlabel("Iteration")
        axes2[i].set_ylabel(var)

    plt.tight_layout()

    for k, v in samples.items():
        print(k)
        if re.match(r"^\d", k):
            # Convert sublists to tuples for hashing if needed
            if v and isinstance(v[0], list):
                hashable_v = [tuple(item) for item in v]
            else:
                hashable_v = v
            uniq = set(hashable_v)
            print(f"{k}: {len(uniq)}")
            print(uniq)

    plt.show()
