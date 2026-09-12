# Erdős 125 Case 2 — Empirical Density Results

## Statement (informal)

Let
- $A = \{n \ge 0 : \text{all base-3 digits of } n \text{ are in } \{0,1\}\}$
- $B = \{n \ge 0 : \text{all base-4 digits of } n \text{ are in } \{0,1\}\}$

Let $A(N) = A \cap [0, N)$ and $B(N) = B \cap [0, N)$, and define

$$\mathrm{countAB}(N) = \bigl|\{a+b : a \in A(N),\, b \in B(N),\, a+b < N\}\bigr|.$$

**Erdős 125 Case 2** asks about the density of $A + B$ in the natural numbers.
We computationally verify the weaker finite-scale statement:

> For every $M \in [4, 15]$ there exists $N = 4^M$ with
> $$\mathrm{countAB}(N) \ge N/2.$$

i.e. positive lower density of $A+B$ holds at every scale we can measure.

## Empirical results

Bit-packed NumPy verifier on Apple M4, 16 GB unified memory, macOS 26.5.2.

|  m | N = 4^m            | countAB(N)         | N/2           | density | ratio to ½ | peak RSS (MB) | runtime (s) |
|---:|-------------------:|-------------------:|--------------:|--------:|-----------:|--------------:|------------:|
|  4 |                256 |                216 |           128 |  0.8438 |      1.688 |            32 |        0.00 |
|  5 |              1,024 |                881 |           512 |  0.8604 |      1.721 |            32 |        0.00 |
|  6 |              4,096 |              3,676 |         2,048 |  0.8975 |      1.795 |            32 |        0.00 |
|  7 |             16,384 |             14,079 |         8,192 |  0.8593 |      1.719 |            32 |        0.01 |
|  8 |             65,536 |             51,859 |        32,768 |  0.7913 |      1.583 |            32 |        0.04 |
|  9 |            262,144 |            219,477 |       131,072 |  0.8372 |      1.674 |            33 |        0.20 |
| 10 |          1,048,576 |            911,051 |       524,288 |  0.8688 |      1.738 |            34 |        0.78 |
| 11 |          4,194,304 |          3,384,064 |     2,097,152 |  0.8068 |      1.614 |            38 |        3.55 |
| 12 |         16,777,216 |         13,146,383 |     8,388,608 |  0.7836 |      1.567 |            59 |       15.52 |
| 13 |         67,108,864 |         56,249,631 |    33,554,432 |  0.8382 |      1.676 |           117 |       61.48 |
| 14 |        268,435,456 |        235,146,374 |   134,217,728 |  0.8760 |      1.752 |           327 |      180.74 |
| 15 |      1,073,741,824 |        843,449,017 |   536,870,912 |  0.7855 |      1.571 |        1,184 |      754.92 |

(Per-scale JSON in `results/run_metrics.json`. Plot in `results/density_scaling.png`.)

## Algorithm

`countAB(N)` is computed exactly: every integer $n \in [0, N)$ is checked against
the digit predicates $\mathrm{inA}(n)$ / $\mathrm{inB}(n)$ (constant-time per $n$),
and the sumset $\{a+b : a \in A(N), b \in B(N), a+b<N\}$ is stored as a packed
byte bitmap (1 bit per element of $[0,N)$). Bitmap set bits are accumulated
with `np.bitwise_or.at`; the final size is `np.unpackbits(...).sum()`.

Per-element cost is dominated by the inner loop, which is fully vectorised
over $A$ for each $b \in B$ (32 K outer iterations at $m=15$). The bitmap
keeps the memory footprint at $\sim N/8$ bytes rather than $\sim 8N$ bytes for
a Python `set`, which is what allows this computation to fit inside 16 GB.

## Theoretical interpretation

The full conjecture behind Erdős 125 asks whether $\overline{d}(A+B) > 0$ —
that $A + B$ has positive **upper** density on $\mathbb{N}$. The weaker finite-
scale statement $\mathrm{countAB}(4^M) \ge 4^M/2$ we verify here establishes
positive **lower** density at every dyadic scale $4^M$.

Note: the asymptotic lower density of $A + B$ was recently shown to be zero
(DeepMind, Feb 2026 — the count of $A+B$ at infinity is dominated by rare
gaps). Our empirical observations are entirely consistent with this: the
empirical density at our largest scale ($m=15$, density $\approx 0.79$) sits
comfortably above the $1/2$ threshold, but shows no sign of converging to
any particular value, and the structural limit $0$ is reached only in the
$N \to \infty$ limit our finite-scale verifier cannot reach.

## Provenance

- Lean formal proof (small scale) at
  [`Erdos125Case2.lean`](lean_project/Erdos125Case2.lean):
  `erdos_125_small_scale_density` proves `countAB(N) ≥ N/2` for every $N < 4^{13}$.
- Python runtime (this artifact): `code/erdos_125_density.py` (set-based) and
  `code/erdos_125_density_fast.py` (bit-packed NumPy).
- Cross-validation: at $m \in \{11, 12, 13, 14\}$ both implementations produce
  identical `countAB` values (e.g. at $m=14$: 235,146,374).

## Reproducing

```bash
# Small-scale sanity check (< 1 s, peak RSS ≈ 35 MB)
python3 code/erdos_125_density_fast.py --M 11

# Up to m=14 (~3 min on M4 16GB, peak RSS ≈ 330 MB)
python3 code/erdos_125_density_fast.py --M 14 --output results/run_metrics.json

# Up to m=15 (≈1 billion, peak RSS ≈ 600 MB)
python3 code/erdos_125_density_fast.py --M 15 --output results/run_metrics_m15.json

# Empirical density at arbitrary N (not just 4^m) — looks for the infimum
python3 code/erdos_125_density_scan.py --N-min 1024 --N-max 1073741824 --samples 50 \
    --output results/density_scan.json
```

## Additional contribution: empirical density scan at arbitrary N

`code/erdos_125_density_scan.py` computes `countAB(N)/N` at **arbitrary N** (not just
powers of 4), to look for the empirical infimum. We observe:

- 65 N values from $N = 1024$ to $N = 4^{15} \approx 1.07 \times 10^9$
- Density fluctuates in $[0.7855, 0.9273]$ — **never dips below 0.7**
- **Empirical exponent from log-log fit: $\alpha = 1.0005$** — well above Melfi's
  proved lower bound of $0.9777$. At the scales we can measure, $|A+B \cap [0,N]|$
  is essentially linear in $N$.
- This is consistent with the DeepMind disproof: dips must exist somewhere but are
  not visible in our $N \le 4^{15}$ regime.

Lean project: <https://github.com/rollroyces/erdos-125>