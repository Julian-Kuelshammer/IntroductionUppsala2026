import Mathlib.Tactic

/-

exact statement1 : The statement is exactly written down in statement1.
rfl : The statement holds by definition, e.g. by reflexivity of equality.
apply lemma2 : According to lemma2 it suffices to prove the hypotheses of lemma2
rw [lemma3] : Use the equality or iff statement lemma3 to replace one thing by an equal/equivalent
  thing
intro x hx : Let x be an element that satisfies the hypothesis hx. (Also possible without x, then
  Assume that hypothesis hx holds. )
have h : claim3 := by proof4 : Introduce an intermediate claim3 whose proof is given in proof4.
simp : Simplify the statement according to some simple facts registered in the database.
ring : We want to prove a statement whose proof is a calculation based on the axioms of a
  commutative ring.
field_simp : We want to prove a statement whose proof is valid in a field. (often one has to supply
  some claims of non-zeroness of denominators by hand beforehand. )
norm_num : The claim is a basic calculation (with actual numbers involved).
grind : general purpose tactic to unfold all definitions and simplify everything.
linarith : Solve basic chains of linear inequalities.
ext : Often used in situations where the goal is an equality of sets and you decompose into a
  statement about the property of its members.

-/
