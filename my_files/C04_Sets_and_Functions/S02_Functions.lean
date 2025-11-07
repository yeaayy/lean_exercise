import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . rintro h a as
    simp at h
    exact h as
  . rintro h b ⟨a, as, rfl⟩
    exact h as

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x ⟨y, ys, yeq⟩
  rw [← h yeq]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  intro b ⟨a, af, aeq⟩
  rw [← aeq]
  exact af

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro b bu
  obtain ⟨a, rfl⟩ := h b
  use a
  constructor
  use bu
  rfl

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro b ⟨a, as, aeq⟩
  rw [← aeq]
  use a
  constructor
  use h as
  rfl

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro a preu
  use h preu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext a
  constructor <;>
  . rintro (preu | prev)
    use Or.inl preu
    use Or.inr prev

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro b ⟨a, ⟨ains, aint⟩, aeq⟩
  rw [← aeq]
  constructor <;> use a

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro b ⟨⟨a₁, a₁s, fa₁_eq_b⟩, ⟨a₂, a₂t, fa₂_eq_b⟩⟩
  have fa₁_eq_fa₂ := fa₁_eq_b
  rw [← fa₂_eq_b] at fa₁_eq_fa₂
  have a₁_eq_a₂ := h fa₁_eq_fa₂

  use a₁
  constructor
  . constructor
    . exact a₁s
    . rw [a₁_eq_a₂]
      exact a₂t
  . exact fa₁_eq_b

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro b ⟨⟨a₁, a₁s, fa₁_eq_b⟩, h⟩
  simp at h
  use a₁
  constructor
  . constructor
    . exact a₁s
    . intro a₁t
      exact h a₁ a₁t fa₁_eq_b
  . exact fa₁_eq_b

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro a ⟨preu, prev⟩
  constructor
  . use preu
  . use prev

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext b
  constructor
  . rintro ⟨⟨a, as, fa_eq_b⟩, bv⟩
    use a
    constructor
    . constructor
      . exact as
      . rw [← fa_eq_b] at bv
        exact bv
    . exact fa_eq_b
  . rintro ⟨a, ⟨as, apv⟩, fa_eq_b⟩
    constructor
    . use a
    . rw [← fa_eq_b]
      exact apv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro b ⟨a, ⟨as, apreu⟩, fa_eq_b⟩
  constructor
  . use a
  . rw [← fa_eq_b]
    exact apreu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro a ⟨as, apreu⟩
  constructor
  . use a
  . exact apreu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro a (as | apreu)
  . left; use a
  . right; use apreu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext b
  constructor
  . rintro ⟨a, ⟨sa, ⟨i, rfl⟩, asa⟩, rfl⟩
    simp
    use i, a
  . rintro ⟨sb, ⟨i, rfl⟩, a, aAi, rfl⟩
    simp
    use a
    constructor
    . use i
    . rfl

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro b ⟨a, U, rfl⟩ sb ⟨i, rfl⟩
  use a
  simp at U
  exact ⟨U i, rfl⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rintro b U
  simp at *
  obtain ⟨a, aAi, rfl⟩ := U i
  use a
  constructor
  . intro j
    obtain ⟨a', a'Aj, fa'_eq_fa⟩ := U j
    rw [← injf fa'_eq_fa]
    exact a'Aj
  . rfl

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext _
  constructor <;> simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext a
  constructor <;> simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnonneg y ynonneg e
  exact (sqrt_inj xnonneg ynonneg).mp e

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg f
  simp at *
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp f with h | h
  . exact h
  . linarith

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x
  constructor
  . intro ⟨y, ynonneg, f⟩
    simp
    rcases sqrt_eq_cases.mp f <;> linarith
  . intro xnonneg
    use x^2
    constructor
    . apply sq_nonneg x
    . apply sqrt_sq xnonneg

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  constructor
  . rintro ⟨y, sq⟩
    simp at *
    calc
      0 ≤ y ^ 2 := sq_nonneg _
      _ ≤ x := by linarith
  . intro xpos
    simp at *
    use √x
    exact sq_sqrt xpos

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . rintro injf a
    exact injf (inverse_spec (f a) (by use a))
  . rintro invf a₁ a₂ eq
    rw [← invf a₁, eq]
    exact invf a₂

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  . rintro surjf b
    exact inverse_spec b (surjf b)
  . rintro invf b
    use inverse f b
    exact invf b

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    have : j ∉ S := by
      intro jS
      rw [h] at h₁
      apply h₁ jS
    contradiction
  have h₃ : j ∉ S := by
    rw [h] at h₁
    contradiction
  contradiction

-- COMMENTS: TODO: improve this
end
