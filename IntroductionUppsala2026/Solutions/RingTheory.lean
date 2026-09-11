import Mathlib

/-- Basic ring theory 2026-06-05, 1 (b)
ℤ₃ × ℤ₄ has characteristic 12. -/
instance : CharP (ZMod 3 × ZMod 4) 12 := by infer_instance -- Some things are just in the library

/-- Basic ring theory 2026-06-05, 2 (a)
Let `R` be a ring with `1 ≠  0`. Let `a ∈  R` such that `a ≠ 0`.
Show that `1 + a ≠  1` and `1 + a ≠  a`. -/
example (R : Type) [Ring R] [Nontrivial R] (a : R) (ha : a ≠ 0) : 1 + a ≠ 1 ∧ 1 + a ≠ a := by
  constructor
  · intro h1a
    apply ha
    grind
  · intro h1a
    rw [add_eq_right] at h1a
    have : (1 : R) ≠ 0 := one_ne_zero
    exact this h1a

open Polynomial

variable (a b : ℚ)

/-- Basic ring theory 2026-06-05, 5
Let `a, b ∈ ℚ` such that `b ≠ 0`. In this exercise we study polynomials `f (x) ∈  ℚ[x]`
such that `a + b√2` is a zero.
(a) Consider the ring homomorphism `φ : ℚ[x] → ℝ`, defined by `φ(p) = p(a + b√2)`.
Let `p(x) = (x - a) ^ 2 - 2 * b ^ 2`. Show that `p(x) ∈ ker φ`. -/
lemma parta :
    (X - C a) ^ 2 - C (2 * b ^ 2) ∈ RingHom.ker (eval₂RingHom (algebraMap ℚ ℝ) (a + b * √2)) := by
  simp
  ring_nf
  norm_num

/-- (b) Show that `p(x) = (x - a) ^ 2 - 2 * b ^ 2` is irreducible in `ℚ[x]`. -/
lemma partb (hb : b ≠ 0) : Irreducible ((X - C a) ^ 2 - C (2 * b ^ 2)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have : ((X - C a) ^ 2 - C 2 * C b ^ 2).natDegree = 2 := by
      compute_degree!
    grind
  · intro x hx
    simp at hx
    have : ((x - a) / b) ^ 2 = 2 := by
      field_simp
      linarith
    apply irrational_sqrt_two
    use |(x - a) / b|
    rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs]
    congr
    exact_mod_cast this

/-- (c) Show that `ker φ = ⟨p⟩`. -/
lemma partc (hb : b ≠ 0) : RingHom.ker (eval₂RingHom (algebraMap ℚ ℝ) (a + b * √2))
    = Ideal.span {((X - C a) ^ 2 - C (2 * b ^ 2))} := by
  have hmax : Ideal.IsMaximal (Ideal.span {((X - C a) ^ 2 - C (2 * b ^ 2))}) := by
    apply PrincipalIdealRing.isMaximal_of_irreducible
    exact partb a b hb
  symm
  apply hmax.eq_of_le
  · apply RingHom.ker_ne_top
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact parta a b

/-- (d) Show that if `a + b√2` is a zero of `f(x) ∈ ℚ[x]`, then so is `a - b√2`. -/
example (hb : b ≠ 0) (f : Polynomial ℚ) (h : eval₂ (algebraMap ℚ ℝ) (a + b * √2) f = 0) :
    eval₂ (algebraMap ℚ ℝ) (a - b * √2) f = 0 := by
  have : f ∈ Ideal.span {((X - C a) ^ 2 - C (2 * b ^ 2))} := by
    rw [← partc]
    · exact h
    · exact hb
  rw [Ideal.mem_span_singleton] at this
  obtain ⟨g, rfl⟩ := this
  rw [eval₂_mul', mul_eq_zero]
  left
  -- from here on the proof is very similar to part (a).
  simp
  ring_nf
  norm_num
