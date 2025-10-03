import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

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
-- ℚ Q 
--
-- ⊢ goal
--
-- ∣ |  (divides)
--
-- ₀ 0 (subscript)
--
-- ↦ map 
--
-- ≅ cong 
-- ≠ =
-- ≡ ==
-- ≣ ===
--
-- ∑ sum
-- 
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

example (a b c :ℤ) (h : a * b ∣ c) : a ∣ c := by
  rcases h with ⟨ k, hk ⟩ 
  rw [hk]
  rw [Int.mul_assoc] 
  exact Int.dvd_mul_right a (b * k)

example (x : ℤ) : ( Even (x^2 + x + 1)) → ( Odd x) := by
  contrapose
  intro hx
  rw [Int.not_odd_iff_even] at hx
  refine Int.not_even_iff_odd.mpr ?_
  unfold Odd 
  unfold Even at hx
    
  (1 + x) ^ n = 1 + nci * x^i
  (1 + x) ^ 1/2 = 1 + 
  ∫ (1 + x) ^ n = x + nci * x^(i+1)/(i+1)
  ∫ (1 - x ^ 2) ^ n = x - nci * x^(i+1) /(i+1)
