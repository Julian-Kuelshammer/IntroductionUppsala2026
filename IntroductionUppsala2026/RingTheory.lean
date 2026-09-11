import Mathlib

/-- Basic ring theory 2026-06-05, 1 (b)
ℤ₃ × ℤ₄ has characteristic 12. -/
instance : CharP (ZMod 3 × ZMod 4) 12 := by sorry

/-- Basic ring theory 2026-06-05, 2 (a)
Let `R` be a ring with `1 ≠  0`. Let `a ∈  R` such that `a ≠ 0`.
Show that `1 + a ≠  1` and `1 + a ≠  a`. -/
example (R : Type) [Ring R] [Nontrivial R] (a : R) (ha : a ≠ 0) : 1 + a ≠ 1 ∧ 1 + a ≠ a := by
  sorry

open Polynomial

variable (a b : ℚ) (hb : b ≠ 0)

/-- Basic ring theory 2026-06-05, 5
Let `a, b ∈ ℚ` such that `b ≠ 0`. In this exercise we study polynomials `f (x) ∈  ℚ[x]`
such that `a + b√2` is a zero.
(a) Consider the ring homomorphism `φ : ℚ[x] → ℝ`, defined by `φ(p) = p(a + b√2)`.
Let `p(x) = (x - a) ^ 2 - 2 * b ^ 2`. Show that `p(x) ∈ ker φ`. -/
example :
    (X - C a) ^ 2 - C (2 * b ^ 2) ∈ RingHom.ker (eval₂RingHom (algebraMap ℚ ℝ) (a + b * √2)) := by
  sorry

/-- (b) Show that `p(x) = (x - a) ^ 2 - 2 * b ^ 2` is irreducible in `ℚ[x]`. -/
example : Irreducible ((X - C a) ^ 2 - C (2 * b ^ 2)) := by
  sorry

/-- (c) Show that `ker φ = ⟨p⟩`. -/
example : RingHom.ker (eval₂RingHom (algebraMap ℚ ℝ) (a + b * √2))
    = Ideal.span {((X - C a) ^ 2 - C (2 * b ^ 2))} := by
  sorry

/-- (d) Show that if `a + b√2` is a zero of `f(x) ∈ ℚ[x]`, then so is `a - b√2`. -/
example (f : Polynomial ℚ) (h : eval₂ (algebraMap ℚ ℝ) (a + b * √2) = 0) :
    eval₂ (algebraMap ℚ ℝ) (a - b * √2) = 0 := by
  sorry
