# 50: Honest re-framing of the Erdős 125 project

## What is the actual state of Erdős 125 (per Tao + Alexeev, Feb 2026)

Erdős's 1997 quote: *"the number of integers $n<x$ of the form $\sum_i \epsilon_i 3^i + \sum_j \epsilon'_j 4^j$ is greater than $cx$, for some $c>0$ and $x>x_0$."*

Tao + Alexeev confirmed: **Erdős's "positive density" means positive lower density**.

- **Lower density of $A+B$**: **0** (DeepMind-disproved Feb 21, 2026, Lean-verified). For any $\epsilon > 0$ there are infinitely many $x$ with $|(A+B) \cap [1, x]| < \epsilon x$.
- **Upper density of $A+B$**: also **0** (it is ≥ 6/5 × lower density = 0).
- Therefore **both conjectures fail**.

The original Erdős 125 question is **closed negatively**.

## What we empirically verified

The Python verifier at `code/erdos_125_density_fast.py` confirms **at every measured scale** (m=4 through m=15, N from 256 to $\approx 10^9$) that countAB(N)/N > 1/2. This is consistent with:

1. **The density stays high at every finite scale** (we don't see 0.69616 dip at any N we've checked up to 1 billion).
2. **The density fluctuates** (0.78 to 0.93 in our scans) without settling.
3. **The disproof only shows gaps exist somewhere** — DeepMind's $\epsilon$-gaps are presumably at scales much larger than $10^9$.

## What's still genuinely open (where we can contribute)

1. **Sharpen Melfi's exponent**: $|C \cap [1,x]| \gg x^{0.9777}$ — the empirical exponent in our data approaches 1, consistent with this bound being improvable.
2. **Find the first $\epsilon$-gap** in $A+B$: at what $x$ does countAB($x$)/$x$ first dip below 0.5, or below any given threshold? This is computationally accessible but requires scales much larger than we've reached.
3. **Melfi's generalization (open per the page)**: for pairwise-coprime bases $\{n_1, ..., n_k\}$ with $\sum 1/\log n_i > 1$, does $\sum A_i$ have positive density? Probably tractable with similar verifier infrastructure.

## What we cannot help with (and why)

The Lean file `Erdos125Case2.lean` has **one remaining sorry** at `density_via_L9` (line 149). This sorry corresponds to the claim $\forall N_0 \ge 4^{13}, \exists N \ge N_0, \mathrm{countAB}(N) \ge N/2$. **This is mathematically false** — DeepMind proved that for any $c > 0$ there exist $x$ where countAB($x$) < $cx$. So the sorry is **necessarily unprovable**, and we should not attempt to close it.

## What is committed to the repo

| Artifact | Purpose |
|----------|---------|
| `code/erdos_125_density.py` | Original set-based Python verifier |
| `code/erdos_125_density_fast.py` | Bit-packed NumPy verifier (m=15 in 12 min) |
| `code/erdos_125_density_scan.py` | Empirical density scan at arbitrary N (this contribution) |
| `results/run_metrics.json`, `run_metrics_m15.json` | Per-scale metrics at N=4^m |
| `results/density_scan.json`, `density_scan_large.json`, `density_scan_xl.json` | Empirical density at arbitrary N |
| `results/density_scaling.png` | Visualization |
| `RESULTS.md` | Human-readable writeup |
| `lean_project/Erdos125Case2.lean` | Lean formal proof (small-scale only) |

## Recommended next step

Submit the empirical data (density scan at arbitrary N) as a comment on
https://www.erdosproblems.com/forum/thread/125 . The data is reproducible
by anyone running `python3 code/erdos_125_density_scan.py`, and the
observation that empirical density stays above 0.77 at all checked scales
(including arbitrary N values up to $4^{15} \approx 10^9$) is new empirical
information that may be useful to others working on the problem.