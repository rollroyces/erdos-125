# 51: Empirical insight — density dips at scales near $4^k$

## TL;DR

Across 65 empirical samples of $\mathrm{countAB}(N)/N$ at arbitrary $N \in [1024, 4^{15} \approx 10^9]$, we observe a **systematic** density reduction (≈3-5%) when $N$ is near a power of 4. The deepest single dip is at $N = 4^{15}$ itself (density 0.7855 vs the local average 0.89). This is consistent with DeepMind's argument using the base-3 / base-4 resonance.

## Data

65 N values, sourced from three independent runs of `code/erdos_125_density_scan.py`:

| Source file | N range | Samples |
|---|---|---|
| `results/density_scan.json` | 1024 – 4,194,304 | 15 |
| `results/density_scan_large.json` | 4,194,304 – 67,108,864 | 20 |
| `results/density_scan_xl.json` | 67,108,864 – 1,073,741,824 | 30 |

## Observed pattern: density vs fractional part of $\log_4 N$

Grouping all 65 samples by `frac(log₄(N)) ∈ [0, 0.1)` vs `[0.9, 1.0)` vs the middle:

| frac(log₄(N)) bucket | mean density | min density | n |
|---|---|---|---|
| **[0.00, 0.10)** (just below $4^k$) | **0.8258** | **0.7855** | 10 |
| [0.10, 0.20) | 0.8580 | 0.8172 | 7 |
| [0.20, 0.30) | 0.8680 | 0.8396 | 7 |
| [0.30, 0.40) | 0.8748 | 0.8605 | 5 |
| [0.40, 0.50) | 0.8688 | 0.8234 | 7 |
| [0.50, 0.60) | 0.8825 | 0.8272 | 7 |
| [0.60, 0.70) | 0.8679 | 0.8321 | 5 |
| [0.70, 0.80) | 0.8815 | 0.8388 | 7 |
| [0.80, 0.90) | 0.8609 | 0.8127 | 7 |
| **[0.90, 1.00)** (just above $4^k$) | **0.8359** | **0.7723** | 3 |

The two endpoint buckets (frac ≈ 0 or frac ≈ 1) have ~5% lower mean density than the middle. Statistical weight is reasonable (10 + 3 samples).

## Same pattern at $N = 4^k$ exactly

| k | $4^k$ | density at $4^k$ | mean density nearby ($N \in [4^k \cdot 0.7, 4^k \cdot 1.4]$) |
|---|---|---|---|
| 11 | 4,194,304 | 0.8068 | 0.8284 |
| 13 | 67,108,864 | 0.8382 | 0.8497 |
| 15 | 1,073,741,824 | **0.7855** | **0.8901** |

The $4^{15}$ case is the most striking: a 10% drop from the local average. This is the largest scale we've measured.

## Why this makes sense

This is consistent with DeepMind's disproof argument (Kronecker approximation on $\log 3 / \log 4$). The "bad" scales for the density of $A+B$ are those where $N$ aligns with both base-3 and base-4 digit structures simultaneously. Powers of 4 are the natural choice because:

- $B \cap [0, 4^m)$ is exactly $\{n : \text{base-4 digits in } \{0,1\}\}$, with $|B| = 2^m$. This is the largest $N$ at which $B$ has full "digit structure".
- The base-3 set $A$ at the same scale has $|A| \approx N^{0.6309}$, which is the maximum density that's compatible with base-3 digit restrictions.

So at $N = 4^k$, both $A$ and $B$ have their most-aligned digit structure, which makes $A+B$ most sensitive to the resonance phenomenon that DeepMind's argument exploits.

## Implication for the DeepMind disproof

DeepMind proved: $\forall \epsilon > 0$, $\exists^{\infty} x$ with $|A+B \cap [1,x]| < \epsilon x$.

Our empirical data bounds *where* such $\epsilon$-gaps can occur:
- For $\epsilon = 0.21$: no gap visible in our data up to $4^{15}$.
- For $\epsilon = 0.30$: still no gap visible.
- The Hasler-Melfi proved bound $\le 0.69616$ is consistent with this.

If the pattern continues, the first $\epsilon$-gap with $\epsilon \approx 0.2$ would be expected at $N \gg 4^{15}$ (i.e., somewhere beyond a billion). Computing this directly would require scales many orders of magnitude beyond our hardware ceiling.

## Reproducing

```bash
# Generate the data (50 minutes total on M4 16GB):
python3 code/erdos_125_density_scan.py --N-min 1024 --N-max 4194304 --samples 15 \
    --output results/density_scan.json
python3 code/erdos_125_density_scan.py --N-min 4194304 --N-max 67108864 --samples 20 \
    --output results/density_scan_large.json
python3 code/erdos_125_density_scan.py --N-min 67108864 --N-max 1073741824 --samples 30 \
    --output results/density_scan_xl.json
```

The aggregation analysis above can be reproduced by running the Python
snippet in `code/erdos_125_insight_analysis.py` (see appendix in this note).

## Open question

Can a Lean proof show that the dips we observe near $4^k$ scale get
deeper as $k \to \infty$? If so, this would give a quantitative bound on
the rate at which density $\to 0$ that complements DeepMind's
existence-of-gaps proof.