import Lake
open Lake DSL

package «erdos125»

@[default_target]
lean_lib «Erdos125»
lean_lib «Erdos125A»
lean_lib «Erdos125B»
lean_lib «Erdos125C»
lean_lib «Erdos125Density»
lean_lib «Erdos125DensityFast»

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"