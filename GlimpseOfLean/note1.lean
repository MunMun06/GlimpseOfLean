import Mathlib.Logic.Basic 

def Even (n : ℤ ) : Prop := ∃ k, n = 2 * k

def Odd (n : ℤ ) : Prop := ∃ k, n = 2 * k + 1
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
-- ∣ |  (divides)
--
-- ₀ 0 (subscript)
--
-- ↦ map 

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

example (x : ℤ ) (h : Even (x^2 + x + 1)) : Odd x := by
    unfold Odd 
    obtain ⟨ k, hk ⟩ := h
    rw [Nat.add_mul_mod_self_right]  
