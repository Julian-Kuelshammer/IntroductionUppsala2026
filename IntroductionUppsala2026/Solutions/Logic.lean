import Mathlib.Tactic

/-
In this file, I introduce some basic tactics to do simple logic exercises, which are the
basics of any mathematical proof. -/

variable (p q r s : Prop)

/-
How to type different symbols:

∧:  \wedge, \and
∨:  \vee, \or
→:  \to, \r
↔:  \leftrightarrow, \lr
¬:  \neg \not
·:  \.
-/

/- Propositional logic -/

-- ∧ intro
example (hp : p) (hq : q) : p ∧ q := by
  constructor   -- consider the two cases seperately
  · exact hp    -- Case 1
  · exact hq    -- Case 2

-- ∧ elim left
example (hpq : p ∧ q) : p := by
  exact hpq.left -- alternative: hpq.1

-- ∧ elim right
example (hpq : p ∧ q) : q := by
  exact hpq.right  -- alternative hpq.2

-- → intro
example (hq : q) : p → q := by
  intro hp    -- assume that p is true and call this assumption hp
  exact hq    -- we know that q holds by hq

-- → elim
example (hp : p) (hpq : p → q) : q := by
  apply hpq   -- By assumption hpq it suffices to prove p.
  exact hp    -- that p holds is assumption hp

-- ↔ intro
example (hpq : p → q) (hqp : q → p) : p ↔ q := by
  constructor     -- there are two directions to prove
  · exact hpq     -- here is the proof of p → q
  · exact hqp     -- here is the proof of q → p

-- ↔ elim left
example (hpq : p ↔ q) : p → q := by
  exact hpq.mp -- alternative hpq.1

-- ↔ elim right
example (hpq : p ↔ q) : q → p := by
  exact hpq.mpr -- alternative hpq.2

-- ¬ intro
example (hfalse : False) : ¬p := by
  intro hp      -- assume for a contradiction that p holds and call this assumption hp for further reference
  exact hfalse  -- False holds by assumption hfalse

-- ¬ elim
example (hp : p) (hnp : ¬p) : False := by
  apply hnp   -- To prove False, using hnp it suffices to prove p
  exact hp    -- That p holds follows from assumption hp

-- ∨ intro left
example (hp : p) : p ∨ q := by
  left      -- We prove p ∨ q by proving that p holds.
  exact hp

-- ∨ intro right
example (hq : q) : p ∨ q := by
  right     -- We prove p ∨ q by proving that q holds
  exact hq

-- ∨ elim
example (hpq : p ∨ q) (hps : p → s) (hqs : q → s) : s := by
  cases hpq with    -- We do a case-by-case analysis according to whether p or q holds
  | inl hp =>       -- This is the case that p holds.
    apply hps
    exact hp
  | inr hq =>       -- This is the case that q holds.
    apply hqs
    exact hq

-- RAA
example (hnnp : ¬¬ p) : p := by
  by_contra hp      -- Assume for a contradiction that ¬p holds and call this assumption hp.
  apply hnnp        -- To prove False, according to hnnp, it suffices to prove ¬p.
  exact hp          -- This is assumption hp.

/- Predicate logic -/

variable (A : Type)
variable (x y z : A)
variable (a : A)
variable (φ : A → Prop)
variable (ψ : Prop)
variable (f : A → A)

-- Some new symbols:
-- ⟨ opening angular bracket \<
-- ⟩ closing angular bracket ⟩

-- This is the rule for = introduction
example : x = x := by
  rfl

-- This is the rule for = elimination
example (hxy : x = y) (hx : φ x) : φ y := by
  rw [←hxy]
  exact hx

-- This is the derived rule that = is a symmetric relation.
example (hxy : x = y) : y = x := by
  apply Eq.symm
  exact hxy

-- This is the derived rule that = is a transitive relation.
example (hxy : x = y) (hyz : y = z) : x = z := by
  apply Eq.trans
  · exact hxy
  · exact hyz

-- This is the derived rule of term substitution for =.
example (hxy : x = y) : f x = f y := by
  rw [hxy]  -- note that rw automatically uses rfl afterwards

-- The rule of existence-introduction.
example (ha : φ a) : ∃ x, φ x := by
  use a -- Since the goal is among the hypotheses here, one doesn't need to argue that it is satisfied, in more complicated examples, one would have to explain afterwards.

-- The rule of existence-elimination.
example (hx : ∃ x, φ x) (h : ∀ x, φ x → ψ) : ψ := by
  obtain ⟨a, ha⟩ := hx -- Let a be the element such that φ(a) holds.
  specialize h a -- Since h holds for all x, it holds in particular for the element a, so φ a → ψ.
  apply h -- Because of h (applied to a) it therefore suffices to prove φ(a).
  exact ha -- We had assumed that a is an element such that φ(a) holds.

-- The rule of forall-elimination.
example (hx : ∀ x, φ x) : φ a := by
  specialize hx a -- Since hx holds for all x, it in particular holds for a.
  exact hx -- The statement is exactly the hypothesis hx, after specialising to a.

-- The rule of forall-introduction.
example (h : ∀ x, φ x) : ∀ x, φ x := by
  intro a -- We want to prove φ(x) for an arbitrary element x, so let's pick an arbitrary element, call it a.
  specialize h a -- That a satisfies property φ is the assumption h, specialised to the element a.
  exact h

/- In the following there are some exercises from a recent Logic and proof techniques I - exam. -/

variable (p q r s : Prop)

/-- Logic and proof technique I. 2026-06-01, 1 (a) -/
example (h1 : (p → q) ∧ (r → s)) (h2 : p ∨ r) (h3 : ¬ s) : q := by
  cases h2 with
  | inl hp =>
    apply h1.1
    exact hp
  | inr hr =>
    exfalso
    apply h3
    apply h1.2
    exact hr

/-- Logic and proof technique I. 2026-06-01, 1 (b) -/
example (h1 : p ∨ q → r) (h2 : ¬ r) : ¬ p ∧ ¬ r := by
  constructor
  · intro hp
    apply h2
    apply h1
    left
    exact hp
  · exact h2

variable (t u : Prop)

/-- Logic and proof technique I. 2026-06-01, 2 -/
example (h1 : r ∨ (s ∧ t)) (h2 : u → ¬r) (h3 : u ∨ t) : t := by
  cases h1 with
  | inl hr =>
    cases h3 with
    | inl hu =>
      exfalso
      apply h2
      · exact hu
      exact hr
    | inr ht =>
      exact ht
  | inr hst =>
    exact hst.2

variable (P Q : A → Prop)
variable (R : A → A → Prop)

/-- Logic and proof technique I. 2026-06-01, 6 (a) -/
example (h1 : ∀ x, P x → ∃ y, R x y) (h2 : ∀ x y, R x y → Q y) (h3 : P (a)) : ∃z, Q z := by
  specialize h1 a
  obtain ⟨b, hb⟩ := h1 h3
  use b
  apply h2
  exact hb

variable (g : A → A)

/-- Logic and proof technique I. 2026-06-01, 6 (b) -/
example (h1 : ∀ x, g x = x) : ∀x, g (f x) = f ( g x) := by
  intro x
  have hgx := h1 x
  have hgfx := h1 (f x)
  rw [hgx, hgfx]
