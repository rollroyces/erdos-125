-- Erdős 125: General count of A = {n : digits of n in base 3 are only 0, 1}

def inA (n : Nat) : Bool :=
  let rec helper (m : Nat) : Bool :=
    if m = 0 then true
    else if m % 3 > 1 then false
    else helper (m / 3)
  helper n
termination_by n => n

def countA (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inA n then acc + 1 else acc) 0

-- Verify |A ∩ [0, 3^k)| = 2^k for small k
example : countA 1 = 1 := by native_decide
example : countA 3 = 2 := by native_decide
example : countA 9 = 4 := by native_decide
example : countA 27 = 8 := by native_decide
example : countA 81 = 16 := by native_decide
example : countA 243 = 32 := by native_decide
example : countA 729 = 64 := by native_decide
example : countA 2187 = 128 := by native_decide
example : countA 6561 = 256 := by native_decide
example : countA 19683 = 512 := by native_decide

-- All these verify |A ∩ [0, 3^k)| = 2^k for k = 0..9
-- Pattern is clear, but proving it for ALL k requires induction

-- Now do the same for B (base 4)
def inB (n : Nat) : Bool :=
  let rec helper (m : Nat) : Bool :=
    if m = 0 then true
    else if m % 4 > 1 then false
    else helper (m / 4)
  helper n
termination_by n => n

def countB (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inB n then acc + 1 else acc) 0

example : countB 1 = 1 := by native_decide
example : countB 4 = 2 := by native_decide
example : countB 16 = 4 := by native_decide
example : countB 64 = 8 := by native_decide
example : countB 256 = 16 := by native_decide
example : countB 1024 = 32 := by native_decide
example : countB 4096 = 64 := by native_decide
example : countB 16384 = 128 := by native_decide

-- All these verify |B ∩ [0, 4^k)| = 2^k for k = 0..7

-- A+B count: |{a + b : a ∈ A, b ∈ B, a + b < N}|
def countAB (N : Nat) : Nat :=
  let A := (List.range N).filter inA
  let B := (List.range N).filter inB
  let sums := A.flatMap fun a => B.map fun b => a + b
  (sums.filter (fun s => s < N)).eraseDups.length

-- The KEY Lean-verified facts about A+B:
example : countAB 100 = 98 := by native_decide
example : countAB 200 = 196 := by native_decide
example : countAB 500 = 424 := by native_decide
example : countAB 1000 = 857 := by native_decide
example : countAB 5000 = 4545 := by native_decide
example : countAB 10000 = 9267 := by native_decide

-- These all match my Python computations