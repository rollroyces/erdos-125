-- Simple Lean 4 test
#check 1 + 1
#check @List.append
#check Nat

-- Try with rfl (reflexivity)
example : 2 + 2 = 4 := rfl

-- Try with decide (decidable proposition)
example : 2 + 2 = 4 := by decide