import Mathlib.Logic.Basic 
-- this is a comment

/- 
  this is a multi-line comment
   -/

-- symbol (everything start with a \)
--
-- ∧ and 
-- ∨ or 
-- ¬ n 
-- → to
-- ↔ if
--
-- ∀ al 
-- ∃ ex
--
-- ℝ R 
-- ℕ N 
-- ℂ C 
-- ℤ Z
--
-- ⊢ goal
--
-- ₀ 0 (subscript)

-- notation
--
-- (f : ℝ → ℝ ) f is a function from reals to reals
--    f n is the same as f(n) on a paper 
-- (x₀ : R) x₀ is a real number

example (p q r : Prop) (h1 : p ∧ (q ∨ r)) (h2 : ¬ (p ∧ q)) : p ∧ r := by
  rw [not_and] at h2
  have ⟨hp, hqr⟩ := h1
  have hnq := h2 hp
  rw [or_iff_not_imp_left] at hqr
  have hr := hqr hnq
  exact ⟨hp, hr⟩

