import Mathlib

section BasicCourse

open Complex
/-- Basic course in mathematics 2025-10-27, 1(a)
Solve the equation `z − iz + 2 + i = 0`.
Write you answer in the form `a + bi` where `a, b ∈ ℝ`. -/

-- My own primitive solution:
example {z : ℂ} : z - I * z + 2 + I = 0 ↔ z = -1 / 2 - 3 / 2 * I := by
  constructor
  · intro hz
    rw [Complex.ext_iff] at *
    simp at *
    grind
  · intro hz
    rw [hz] -- substitute in z
    ring_nf -- normalise using the ring axioms
    rw [I_sq] -- use `I ^ 2 = -1`
    ring -- normalise using the ring axioms

-- Claude's solution using the `linear_combination` tactic.
-- The first solution it gave was not pedagogical, so I promted it a bit more.
example {z : ℂ} : z - I * z + 2 + I = 0 ↔ z = -1 / 2 - 3 / 2 * I := by
  constructor
  · intro hz
    have hre : z.re + z.im + 2 = 0 := by simpa using congrArg Complex.re hz
    have him : z.im - z.re + 1 = 0 := by simpa using congrArg Complex.im hz
    rw [Complex.ext_iff]
    norm_num
    constructor <;> linarith
  · intro hz
    rw [hz] -- substitute in
    linear_combination (3 / 2 : ℂ) * I_sq

-- My own primitive solution
example {x : ℝ} : |x| = 3 - 2 * x ↔ x = 1 := by
  constructor
  · intro hx
    rcases eq_or_eq_neg_of_abs_eq hx with h | h
    · linarith
    · have h' : x = 3 := by linarith
      rw [h'] at hx
      norm_num at hx
  · intro rfl
    norm_num

-- Claude's solution using a cleverer case split.
example {x : ℝ} : |x| = 3 - 2 * x ↔ x = 1 := by
  constructor
  · intro hx
    rcases abs_cases x with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> linarith
  · intro rfl
    norm_num

section onec

open Finset

/-- Basic course in mathematics 2025-10-27, 1 (c)
How many subsets with exactly 4 elements can you choose from a set with 10 elements? -/

-- My own solution.
example {α : Type} (S : Finset α) (h : #S = 10) : #(powersetCard 4 S) = 210 := by
  rw [card_powersetCard, h]
  norm_num [Nat.choose]

-- Claude's solution, essentially the same.
example {α : Type} (S : Finset α) (h : #S = 10) : #(powersetCard 4 S) = 210 := by
  rw [card_powersetCard, h]
  decide

end onec

section oned

open Set

-- My own solution. Here I think my own one is a bit nicer since it uses mathlib lemmas where
-- possible.
example {A B C : Set ℝ} (hA : A = Ioo 0 3) (hB : B = Ioo 1 5) (hC : C = Icc 2 4) :
    (A ∩ B) ∪ C = Ioc 1 4 ∧ A ∩ (B ∪ C) = Ioo 1 3 := by
  constructor
  · have : A ∩ B = Ioo 1 3 := by
      rw [hA, hB, Ioo_inter_Ioo]
      norm_num
    rw [this, hC]
    ext x
    constructor
    · intro h
      simp only [mem_union, mem_Ioo, mem_Icc, mem_Ioc] at *
      rcases h with h | h <;> constructor <;> linarith
    · intro h
      simp only [mem_Ioc, mem_union, mem_Ioo, mem_Icc] at *
      rcases lt_or_ge x 3 with h' | h'
      · left
        exact ⟨h.1, h'⟩
      · right
        constructor <;> linarith
  · have : B ∪ C = Ioo 1 5 := by
      rw [hB, hC, union_eq_left, Icc_subset_Ioo_iff (by norm_num)]
      norm_num
    rw [this, hA, Ioo_inter_Ioo]
    norm_num

-- Claude's primitive solution.
example {A B C : Set ℝ} (hA : A = Ioo 0 3) (hB : B = Ioo 1 5) (hC : C = Icc 2 4) :
    (A ∩ B) ∪ C = Ioc 1 4 ∧ A ∩ (B ∪ C) = Ioo 1 3 := by
  subst hA hB hC
  constructor
  · ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro (⟨⟨h₁, h₂⟩, h₃, h₄⟩ | ⟨h₁, h₂⟩) <;> constructor <;> linarith
    · rintro ⟨h₁, h₂⟩
      rcases lt_or_ge x 2 with h | h
      · exact Or.inl ⟨⟨by linarith, by linarith⟩, h₁, by linarith⟩
      · exact Or.inr ⟨h, h₂⟩
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_Ioo, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩⟩ <;> constructor <;> linarith
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨by linarith, h₂⟩, Or.inl ⟨h₁, by linarith⟩⟩

end oned

/-- Basic course in mathematics 2025-10-27, 1 (e)
Compute `∑_{k=1}^10 (1 + 2k)`. -/
-- A computer solution, just add the numbers together and they coincide by the definition of
-- addition and multiplication in the natural numbers.
example : ∑ k ∈ Finset.Icc 1 10, (1 + 2 * k) = 120 := by
  rfl

-- Here is a more honest solution, but it is a bit hacky because Lean prefers natural numbers to
-- start at 0.
example : ∑ k ∈ Finset.Icc 1 10, (1 + 2 * k) = 120 := by
  have h1 : ∑ k ∈ Finset.Icc 1 10, (1 : ℕ) = 10 := by
    rw [Finset.sum_const, Nat.card_Icc]
    norm_num
  have h2 : ∑ k ∈ Finset.Icc 1 10, k = 55 := by
    have hr : (∑ i ∈ Finset.range 11, i) = 11 * 10 / 2 := Finset.sum_range_id 11
    rw [show Finset.range 11 = insert 0 (Finset.Icc 1 10) from by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
      Finset.sum_insert (by simp), Nat.zero_add] at hr
    rw [hr]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]
  norm_num

/-- Basic course in mathematics 2025-10-27, 7
Show by induction that `1 * 2 + 2 * 2 ^ 2 + 3 * 2 ^ 3 + · · · + n * 2 ^ n = (n − 1)* 2^ (n+1) + 2`
for all natural numbers `n ≥ 1`. -/
example {n : ℕ} : ∑ k ∈ Finset.range (n + 2), k * 2 ^ k = n * 2 ^ (n + 2) + 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

end BasicCourse
