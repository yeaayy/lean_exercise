import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro N Nmax
  show |s N + t N - (a + b)| < ε

  have is := hs N (le_of_max_le_left Nmax)
  have it := ht N (le_of_max_le_right Nmax)

  have aux1: |s N + t N - (a + b)| = |s N - a + (t N - b)| := by congr; linarith

  rw [aux1]
  convert lt_of_le_of_lt (abs_add_le _ _) (add_lt_add_of_lt_of_lt is it)
  . norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have ε_div_abs_c_pos := div_pos εpos acpos
  rcases cs (ε / |c|) (ε_div_abs_c_pos) with ⟨n1, h1⟩

  use n1
  intro n2 h2
  calc
    |c * s n2 - c * a| = |(s n2 - a) * c| := by congr; linarith
    _ = |s n2 - a| * |c| := by apply abs_mul
    _ < ε := by
      convert mul_lt_mul (h1 n2 h2) (le_refl _) acpos (le_of_lt ε_div_abs_c_pos)
      rw [div_mul_cancel₀ ε (fun aczero ↦ h (abs_eq_zero.mp aczero))]

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro N1 h1
  have h2 := h N1 h1
  obtain ⟨ha, hb⟩ := abs_lt.mp h2
  apply abs_lt.mpr
  constructor <;>
  . by_cases apos : 0 < a
    . rw [abs_of_pos apos]
      linarith
    . rw [abs_of_nonpos (le_of_not_lt apos)]
      linarith

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro Nmax hnmax
  rw [sub_zero, abs_mul, ← mul_div_cancel_left₀ ε (ne_of_gt Bpos), mul_div_assoc]

  apply mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
  exact le_of_lt (h₀ Nmax (le_of_max_le_left hnmax))
  convert (h₁ Nmax (le_of_max_le_right hnmax))
  . norm_num
  exact abs_nonneg _
  exact Bpos

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := abs_pos.mpr (by intro abzero; exact abne (sub_eq_zero.mp abzero))
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_max_left Na Nb)
  have absb : |s N - b| < ε := hNb N (le_max_right Na Nb)
  have : |a - b| < |a - b| := by
    calc
      |a - b| = |(s N - b) - (s N - a)| := by congr 1; linarith
      _       ≤ |s N - b| + |s N - a|   := abs_sub _ _
      _       < ε + ε                   := add_lt_add_of_lt_of_lt absb absa
      _       = |a - b|                 := by rw [← mul_two, ← eq_div_iff two_ne_zero]
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
