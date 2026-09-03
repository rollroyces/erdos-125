/-- Erdős 125: General count of A = {n : digits of n in base 3 are only 0, 1} -/

def inA (n : Nat) : Bool :=
  let rec helper (m : Nat) : Bool :=
    if m = 0 then true
    else if m % 3 > 1 then false
    else helper (m / 3)
  helper n

def countA (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inA n then acc + 1 else acc) 0

/-- Verify |A ∩ [0, 3^k)| = 2^k for small k using native_decide. -/
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
example : countA 59049 = 1024 := by native_decide

/-- Verify B = {n : digits of n in base 4 are only 0, 1} -/
def inB (n : Nat) : Bool :=
  let rec helper (m : Nat) : Bool :=
    if m = 0 then true
    else if m % 4 > 1 then false
    else helper (m / 4)
  helper n

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

/-- Verify |A+B ∩ [0,N)| for various N -/
def countAB (N : Nat) : Nat :=
  let A := (List.range N).filter inA
  let B := (List.range N).filter inB
  let sums := A.flatMap fun a => B.map fun b => a + b
  (sums.filter (fun s => s < N)).eraseDups.length

example : countAB 100 = 98 := by native_decide
example : countAB 1000 = 857 := by native_decide
example : countAB 10000 = 9267 := by native_decide

/-- Inductive structure verification: countA(2N) - countA(N) = countA(N) for N = 3^k -/
example : countA 6 - countA 3 = 2 := by native_decide
example : countA 18 - countA 9 = 4 := by native_decide
example : countA 54 - countA 27 = 8 := by native_decide
example : countA 162 - countA 81 = 16 := by native_decide

/-- Third range verification: countA(3N) - countA(2N) = 0 for N = 3^k -/
example : countA 9 - countA 6 = 0 := by native_decide
example : countA 27 - countA 18 = 0 := by native_decide
example : countA 81 - countA 54 = 0 := by native_decide
