import Mathlib

section BasicCourse

open Complex
/-- Basic course in mathematics 2025-10-27, 1 (a)
Solve the equation `z − iz + 2 + i = 0`.
Write you answer in the form `a + bi` where `a, b ∈ ℝ`. -/
example {z : ℂ} : z - I * z + 2 + I = 0 ↔ z = -1 / 2 - 3 / 2 * I := by
  sorry

/-- Basic course in mathematics 2025-10-27, 1 (b)
Solve the equation `|x| = 3 − 2x` for `x ∈ ℝ`. -/
example {x : ℝ} : |x| = 3 - 2 * x ↔ x = 1 := by
  sorry

section onec

open Finset

/-- Basic course in mathematics 2025-10-27, 1 (c)
How many subsets with exactly 4 elements can you choose from a set with 10 elements? -/
example {α : Type} (S : Finset α) (h : #S = 10) : #(powersetCard 4 S) = 210 := by
  sorry

end onec

section oned

open Set

/-- Basic course in mathematics 2025-10-27, 1 (d)
Determine the sets `(A ∩ B) ∪ C` and `A ∩ (B ∪ C)`, where A = (0, 3),
B = (1, 5) and C = [2, 4]. -/
example {A B C : Set ℝ} (hA : A = Ioo 0 3) (hB : B = Ioo 1 5) (hC : C = Icc 2 4) :
    (A ∩ B) ∪ C = Ioc 1 4 ∧ A ∩ (B ∪ C) = Ioo 1 3 := by
  sorry

end oned

/-- Basic course in mathematics 2025-10-27, 1 (e)
Compute `∑_{k=1}^10 (1 + 2k)`. -/
example : ∑ k ∈ Finset.Icc 1 10, (1 + 2 * k) = 120 := by
  sorry

/- Basic course in mathematics 2025-10-27, 7
Show by induction that `1 * 2 + 2 * 2 ^ 2 + 3 * 2 ^ 3 + · · · + n * 2 ^ n = (n − 1)* 2^ (n+1) + 2`
for all natural numbers `n ≥ 1`.
-- Here I'll hide even the setup of the Lean since this is maybe the most interesting part.-/

end BasicCourse
