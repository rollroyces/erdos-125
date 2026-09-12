/-
  Erdos125CountABm15.lean

  Native_decide theorems for countAB at the m=15 scale (N = 4^15 = 1,073,741,824).

  These theorems are separated from Erdos125CountAB.lean because
  `native_decide` at this scale requires >8 GB of RAM and is OOM-killed
  on M4 16 GB systems. Build with:

    lake build Erdos125CountABm15

  on a system with ≥16 GB RAM. Expected runtime: 12-20 hours per theorem.

  All values verified empirically:
    - countAB_in_0_N_hs (4^15) = 843449017
    - density 0.7855, well above the 1/2 threshold
    - Lower than density at 4^14 (which is 0.8760)

  See notes/52_FOCUS_V_SHAPE.md for the empirical V-shape around 4^15.
-/

import Mathlib
import Erdos125
import Erdos125CountAB

namespace Erdos125CountABm15

open Erdos125 Erdos125CountAB

/-- `countAB_in_0_N_hs (4^15) = 843449017`.

    Exact value of the count at N = 4^15 = 1,073,741,824 (≈ 1 billion).
    Empirical density: 843449017 / 1073741824 ≈ 0.7855. -/
theorem countAB_in_0_N_hs_4_15_eq : countAB_in_0_N_hs (4^15) = 843449017 := by
  native_decide

/-- Density at N = 4^15 is between 0.78 and 0.79.

    `countAB * 100 > 4^15 * 78` and `countAB * 100 < 4^15 * 79`. -/
theorem countAB_in_0_N_hs_4_15_density_band :
    countAB_in_0_N_hs (4^15) * 100 > (4^15) * 78 ∧
    countAB_in_0_N_hs (4^15) * 100 < (4^15) * 79 := by
  native_decide

/-- Density at N = 4^15 is strictly less than at N = 4^14.

    Pins down the empirical observation from the density scan (notes/51):
    density is lower at N = 4^15 than at N = 4^14.

    Concretely: 843449017 * 4^14 < 235146374 * 4^15
              ⟺ 843449017 * 4 < 235146374 * 16
              ⟺ 3373796068 < 3762341984. -/
theorem countAB_in_0_N_hs_4_15_dip :
    countAB_in_0_N_hs (4^15) * (4^14) < countAB_in_0_N_hs (4^14) * (4^15) := by
  native_decide

/-- Density is below 0.9 at N = 4^15.

    countAB(4^15) < 4^15 * 9/10, i.e., 843449017 * 10 < 9 * 4^15. -/
theorem countAB_in_0_N_hs_4_15_below_nine_tenths :
    countAB_in_0_N_hs (4^15) * 10 < 9 * (4^15) := by
  native_decide

end Erdos125CountABm15